/** Fresh Pi SDK loop: one stdin prompt, native tools/MCP and metered compaction. */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

export const MODEL = "gpt-6.1-sol";
export const TOKEN_ENV = "LRH_SERIAL_MODEL_TOKEN";
export const NATIVE_TOOL_NAMES = ["read", "bash", "edit", "write", "grep", "find", "ls"];
export const TOOL_NAMES = [...NATIVE_TOOL_NAMES, "mcp__lean_feedback__edit_check"];
const FEEDBACK_TOOL_NAMES = new Set(["edit_check", "compare_candidates", "score_candidate", "retrieve_lemmas"]);

export function feedbackToolNames(settings) {
  const names = settings.enabled_tools ?? ["edit_check"];
  if (!Array.isArray(names) || names[0] !== "edit_check" || new Set(names).size !== names.length
    || names.some((name) => !FEEDBACK_TOOL_NAMES.has(name))) {
    throw new Error("Invalid capsule feedback tool allowlist");
  }
  // Feature-enabled capsules must carry the Python contract's canonical list.
  if (!settings.enabled_tools && (settings.candidate_batches || settings.goal_retrieval)) {
    throw new Error("Feature-enabled capsule is missing its feedback tool allowlist");
  }
  return names;
}

export function feedbackTimeout(settings, names = feedbackToolNames(settings)) {
  const scoreRequests = 5 + (settings.compatibility_roots?.length ?? 0);
  const leanRequests = settings.candidate_batches ? 4 * scoreRequests
    : names.includes("score_candidate") ? scoreRequests : 4;
  return leanRequests * (settings.timeout_seconds ?? 600) + 30;
}
export function normalizedToolResult(event) {
  // Pi's MCP adapter retains isError in its result; SDK event flags can differ.
  // Preserve the raw payload and the protocol flag, without reclassifying an
  // ordinary valid=false proof verdict as a failed tool request.
  return { type: event.type, tool: event.toolName, tool_call_id: event.toolCallId,
    is_error: event.isError === true || event.result?.isError === true, result: event.result };
}

export function sanitizedEnvironment(environment) {
  // Tools need Lean's capsule/broker capabilities, never inference credentials.
  const safe = {};
  for (const [key, value] of Object.entries(environment)) {
    if (["HOME", "PATH", "LANG", "LC_ALL", "LC_CTYPE", "TERM", "SHELL", "USER", "LOGNAME",
      "TMPDIR", "ELAN_HOME", "LEAN_NUM_THREADS", "OMP_NUM_THREADS", "E6_ENVIRONMENTS_ROOT",
      "E6_RUNTIME_ROOT", "PI_CODING_AGENT_DIR"].includes(key) || key.startsWith("LEAN_REFACTOR_")) {
      if (key !== TOKEN_ENV && !/(API_KEY|ACCESS_TOKEN|REFRESH_TOKEN|PASSWORD|SECRET|CREDENTIAL)/i.test(key)) {
        safe[key] = value;
      }
    }
  }
  return safe;
}

function argumentsFrom(argv) {
  const args = {};
  for (let i = 0; i < argv.length; i++) {
    const name = argv[i];
    if (name === "--preflight") { args.preflight = true; continue; }
    if (!["--package", "--capsule", "--catalog", "--relay", "--python", "--feedback-script"].includes(name)
      || !argv[i + 1]) throw new Error(`Unexpected or incomplete option: ${name}`);
    args[name.slice(2).replaceAll("-", "_")] = argv[++i];
  }
  for (const name of ["package", "capsule", "catalog", "python", "feedback_script"]) {
    if (!args[name]) throw new Error(`Missing --${name.replaceAll("_", "-")}`);
  }
  return args;
}

export function catalogModel(catalog) {
  const row = catalog.models?.find((item) => item.slug === MODEL);
  if (!row || !row.supported_reasoning_levels?.some((item) => item.effort === "xhigh")
    || !Number.isSafeInteger(row.context_window) || row.context_window <= 0) {
    throw new Error("Frozen catalog must include Sol 6.1 xhigh and its native context window");
  }
  return { id: MODEL, name: row.display_name || MODEL, api: "openai-responses", reasoning: true,
    input: ["text"], contextWindow: row.context_window,
    // The catalog has no output limit. This metadata placeholder is never sent:
    // supportsMaxOutputTokens=false below preserves native unlimited Responses output.
    maxTokens: row.context_window, cost: { input: 0, output: 0, cacheRead: 0, cacheWrite: 0 },
    thinkingLevelMap: { off: null, minimal: "low", low: "low", medium: "medium", high: "high",
      xhigh: "xhigh", max: "xhigh" },
    // This lets Pi SEND the strict flag. MCP tools do not request constrained
    // sampling, so its converter emits strict:false with their original optional
    // schema. Omitting the flag lets Responses normalize that schema into strict mode.
    compat: { supportsMaxOutputTokens: false, supportsStrictMode: true } };
}

async function sdkModules(packageDirectory) {
  const modules = path.resolve(packageDirectory, "../..");
  const load = (file) => import(pathToFileURL(file).href);
  const [sdk, ai, responses, extensionLoader, mcp] = await Promise.all([
    load(path.join(packageDirectory, "dist/index.js")),
    load(path.join(modules, "@earendil-works/pi-ai/dist/index.js")),
    load(path.join(modules, "@earendil-works/pi-ai/dist/api/openai-responses.js")),
    load(path.join(packageDirectory, "dist/core/extensions/loader.js")),
    load(path.join(modules, "@earendil-works/pi-mcp/dist/index.js")),
  ]);
  return { sdk, ai, responses, extensionLoader, mcp };
}

function safeError(error, token) {
  let message = error instanceof Error ? error.message : String(error);
  if (token) message = message.replaceAll(token, "[relay capability redacted]");
  return message;
}

/** Exported for offline scripted-provider checks; production always supplies the native relay stream. */
export async function createFreshSession(args, { token, streamSimple, emit = () => {} } = {}) {
  process.env.PI_OFFLINE = "1";
  const { sdk, ai, responses, extensionLoader, mcp } = await sdkModules(args.package);
  const capsule = path.resolve(args.capsule);
  const agentDir = path.join(capsule, ".native-home/.pi/agent");
  const definition = catalogModel(JSON.parse(fs.readFileSync(args.catalog, "utf8")));
  let baseUrl = "http://127.0.0.1:1/v1"; // Offline metadata sessions have no usable inference route.
  if (args.relay) {
    const relay = new URL(args.relay);
    if (relay.protocol !== "http:" || !["127.0.0.1", "localhost", "[::1]"].includes(relay.hostname)
      || relay.username || relay.password || relay.search || relay.hash) {
      throw new Error("Pi inference requires a plain loopback HTTP relay URL");
    }
    baseUrl = args.relay.replace(/\/$/, "");
  }
  const modelRuntime = await sdk.ModelRuntime.create({ credentials: new ai.InMemoryCredentialStore(),
    modelsPath: null, modelsStore: new ai.InMemoryModelsStore(), refreshOnCreate: false,
    allowModelNetwork: false });
  const providerStream = streamSimple ?? ((model, context, options = {}) => {
    if (model.id !== MODEL || model.provider !== "e6" || model.baseUrl !== baseUrl || !token) {
      throw new Error("Pi request escaped the pinned metered model");
    }
    // The same closure handles ordinary turns, retries, and native compaction.
    // Never serialize SDK context/options or the capability into event files.
    return responses.stream(model, context, { ...options, apiKey: token, reasoningEffort: "xhigh",
      serviceTier: "default", reasoningSummary: null, transport: "sse", env: {} });
  });
  modelRuntime.registerProvider("e6", { name: "E6 metered Responses", baseUrl, api: "openai-responses",
    apiKey: "e6-relay-only", models: [definition], streamSimple: providerStream });
  const model = modelRuntime.getModel("e6", MODEL);
  if (!model) throw new Error("Pi did not register the pinned model");

  const safeEnv = sanitizedEnvironment(process.env);
  const feedbackConfig = path.join(capsule, "feedback-config.json");
  if (!fs.existsSync(feedbackConfig)) throw new Error("Capsule feedback-config.json is missing");
  const feedbackSettings = JSON.parse(fs.readFileSync(feedbackConfig, "utf8"));
  const feedbackNames = feedbackToolNames(feedbackSettings);
  const toolNames = [...NATIVE_TOOL_NAMES, ...feedbackNames.map((name) => `mcp__lean_feedback__${name}`)];
  const settingsManager = sdk.SettingsManager.inMemory({ defaultTools: toolNames, cacheWarming: "off" });
  const timeout = feedbackTimeout(feedbackSettings, feedbackNames);
  const servers = [{ name: "lean_feedback", scope: "extension", source: "e6:lean-feedback",
    config: { command: args.python, args: [args.feedback_script, "--config", feedbackConfig, "--serve"],
      cwd: capsule, exposure: "hidden", toolExposure: Object.fromEntries(feedbackNames.map((name) => [name, "direct"])),
      timeout,
      description: "Capsule-scoped Lean edit and source-bound feedback" } }];
  const runtime = sdk.createExtensionRuntime();
  const eventBus = sdk.createEventBus();
  const extensions = [];
  // Explicit factory loading avoids DefaultResourceLoader's package/global/project discovery.
  const registerShell = (pi) => pi.registerTool(sdk.createBashToolDefinition(capsule, {
    shellPath: "/bin/bash", exposeSessionEnvironment: false,
    spawnHook: (context) => ({ ...context, env: sanitizedEnvironment(context.env) }) }));
  const transports = [];
  const close = async () => { await Promise.allSettled(transports.map((transport) => transport.close())); };
  const nativeMcp = sdk.createMcpExtension({ loadConfig: () => ({ servers, errors: [], autoEnableCodemode: false }),
    createTransport: (entry) => {
      const transport = new mcp.StdioTransport({ command: entry.config.command,
        args: entry.config.args, cwd: capsule, env: safeEnv, inheritEnv: false, stderr: "pipe" });
      transports.push(transport);
      return transport;
    },
    logPath: path.join(agentDir, "mcp.log"),
    openUrl: () => { throw new Error("MCP login is unavailable in proof agents"); },
    startupWaitMs: 20000 });
  for (const [name, factory] of [["e6-shell", registerShell], ["e6-mcp", nativeMcp]]) {
    extensions.push(await extensionLoader.loadExtensionFromFactory(factory, capsule, eventBus, runtime, name));
  }
  const loader = {
    getExtensions: () => ({ extensions, errors: [], runtime }),
    getSkills: () => ({ skills: [], diagnostics: [] }),
    getPrompts: () => ({ prompts: [], diagnostics: [] }),
    getThemes: () => ({ themes: [], diagnostics: [] }),
    getAgentsFiles: () => ({ agentsFiles: [] }),
    getSystemPrompt: () => undefined, getSystemPromptSource: () => undefined,
    getAppendSystemPrompt: () => [], getAppendSystemPromptSources: () => [],
    extendResources: () => {}, reload: async () => {},
  };
  const { session } = await sdk.createAgentSession({ cwd: capsule, agentDir, modelRuntime, model,
    thinkingLevel: "xhigh", scopedModels: [{ model, thinkingLevel: "xhigh" }],
    settingsManager, sessionManager: sdk.SessionManager.inMemory(capsule), resourceLoader: loader,
    tools: toolNames });
  session.subscribe((event) => {
    // Native transcript events contain SDK context objects; project only useful fields.
    if (event.type === "message_end") {
      const message = event.message;
      if (message.role === "assistant") emit({ type: "assistant", stop_reason: message.stopReason,
        content: message.content, usage: message.usage, error: message.errorMessage });
    } else if (event.type === "tool_execution_start") {
      emit({ type: event.type, tool: event.toolName, tool_call_id: event.toolCallId, arguments: event.args });
    } else if (event.type === "tool_execution_end") {
      emit(normalizedToolResult(event));
    } else if (["agent_start", "agent_settled", "compaction_start", "compaction_end", "auto_retry_start",
      "auto_retry_end", "summarization_retry_scheduled"].includes(event.type)) {
      emit({ type: event.type, aborted: event.aborted, reason: event.reason, will_retry: event.willRetry,
        error: event.errorMessage ?? event.finalError, attempt: event.attempt, delay_ms: event.delayMs });
    }
  });
  try {
    await session.bindExtensions({});
  } catch (error) {
    await close(); session.dispose();
    throw error;
  }
  // Binding connects direct MCP asynchronously. Wait only for startup/schema, never inference.
  const startupDeadline = Date.now() + 20000;
  while (feedbackNames.some((name) => !session.getActiveToolNames().includes(`mcp__lean_feedback__${name}`)) && Date.now() < startupDeadline) {
    await new Promise((resolve) => setTimeout(resolve, 25));
  }
  const names = session.getActiveToolNames();
  if (names.some((name) => !toolNames.includes(name))
    || toolNames.filter((name) => !name.startsWith("mcp__")).some((name) => !names.includes(name))) {
    await close(); session.dispose();
    throw new Error("Pi tool inventory differs from the proof-agent allowlist");
  }
  if (session.thinkingLevel !== "xhigh" || session.messages.length !== 0) {
    await close(); session.dispose();
    throw new Error("Pi session is not fresh Sol 6.1 xhigh");
  }
  const tools = session.getAllTools().filter((tool) => names.includes(tool.name))
    .map((tool) => ({ name: tool.name, parameters: tool.parameters }));
  if (tools.some((tool) => tool.parameters?.type !== "object")) {
    await close(); session.dispose();
    throw new Error("Pi tool metadata contains a non-object parameter schema");
  }
  return { session, close, modelRuntime, sdk, ai, definition,
    optionalMcpStatus: feedbackNames.every((name) => names.includes(`mcp__lean_feedback__${name}`)) ? "passed" : "failed",
    tools };
}

export async function main(argv = process.argv.slice(2)) {
  const args = argumentsFrom(argv);
  // Consume before importing Pi or creating any tool. All descendants inherit the clean environment.
  let token;
  try { token = fs.readFileSync(3, "utf8").trim(); } finally {
    try { fs.closeSync(3); } catch (error) { if (error.code !== "EBADF") throw error; }
  }
  const safeEnv = sanitizedEnvironment(process.env);
  for (const key of Object.keys(process.env)) delete process.env[key];
  Object.assign(process.env, safeEnv, { PI_OFFLINE: "1" });
  const emit = (event) => {
    const serialized = JSON.stringify(event);
    process.stdout.write((token ? serialized.replaceAll(token, "[relay capability redacted]") : serialized) + "\n");
  };
  let session;
  let close;
  let signalReceived;
  const onSignal = (signal) => { signalReceived = signal; void session?.abort(); };
  const interrupt = () => onSignal("SIGINT"), terminate = () => onSignal("SIGTERM");
  process.on("SIGINT", interrupt); process.on("SIGTERM", terminate);
  try {
    if (!args.preflight && (!token || !args.relay)) throw new Error("Pi proof agent requires its metered relay capability");
    const prepared = await createFreshSession(args, { token, emit });
    session = prepared.session;
    close = prepared.close;
    const metadata = { model: MODEL, reasoning_effort: session.thinkingLevel, pi_version: prepared.sdk.VERSION,
      context_window: prepared.definition.contextWindow, fresh_in_memory: true,
      context_files: [], skills: [], prompt_templates: [], active_tools: session.getActiveToolNames(),
      model_requests: 0, compaction: "native Pi defaults; same metered model", output_token_cap: null };
    metadata.optional_mcp_status = prepared.optionalMcpStatus;
    if (prepared.optionalMcpStatus === "failed") {
      metadata.E6_preparation_allowed = true;
      metadata.E6_preparation_note = "Optional native MCP unavailable; documented shell feedback wrappers remain available";
    }
    if (args.preflight) {
      emit({ type: "preflight", status: "passed", ...metadata, tools: prepared.tools });
      return 0;
    }
    emit({ type: "pi_start", ...metadata });
    let prompt = "";
    for await (const chunk of process.stdin) prompt += chunk;
    if (!prompt.trim()) throw new Error("Pi prompt on stdin is empty");
    if (signalReceived) throw new Error(`Pi cancelled by ${signalReceived}`);
    await session.prompt(prompt, { expandPromptTemplates: false });
    const last = [...session.messages].reverse().find((message) => message.role === "assistant");
    const rawFinal = session.getLastAssistantText() ?? "";
    const final = token ? rawFinal.replaceAll(token, "[relay capability redacted]") : rawFinal;
    fs.writeFileSync(path.join(args.capsule, "pi-final.txt"), final + (final.endsWith("\n") ? "" : "\n"));
    if (signalReceived || !last || ["error", "aborted", "length", "pending"].includes(last.stopReason)) {
      throw new Error(signalReceived ? `Pi cancelled by ${signalReceived}` : last?.errorMessage || `Pi ended with ${last?.stopReason ?? "no response"}`);
    }
    emit({ type: "pi_final", status: "completed", text: final });
    return 0;
  } catch (error) {
    const message = safeError(error, token);
    emit({ type: args.preflight ? "preflight" : "pi_error", status: "failed", error: message });
    return signalReceived === "SIGINT" ? 130 : signalReceived === "SIGTERM" ? 143 : 1;
  } finally {
    process.removeListener("SIGINT", interrupt); process.removeListener("SIGTERM", terminate);
    if (session) {
      await session.abort();
      // Dispose is the SDK's documented session shutdown boundary.
      session.dispose();
    }
    await close?.();
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url))) {
  process.exitCode = await main();
}
