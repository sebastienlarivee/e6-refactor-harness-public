"""Frozen policy and scheduler integration; workers/providers are scripted."""
from argparse import Namespace
from copy import deepcopy
from dataclasses import replace
from decimal import Decimal
from pathlib import Path
from types import ModuleType, SimpleNamespace
import sys

import pytest

from e6 import run as core
from e6.experiment import DEFAULT_RUN_SPEC, blocking_unknown_usage
from harness import cli, runner
from harness.config import RunConfig, digest
from tests.test_product_config import document
from tests.test_product_runner import cell, charge

COST_SPEC = replace(DEFAULT_RUN_SPEC, stopping_policy='cost')


def test_new_default_and_historical_missing_recovery_keep_distinct_frozen_identity(tmp_path):
    new = RunConfig.from_dict(document(), base=tmp_path)
    assert new.recovery_policy == new.to_dict()['recovery_policy'] == 'generation-v1'
    old = new.to_dict(); old.pop('recovery_policy')
    fingerprint = digest(old)
    loaded = RunConfig.from_frozen_dict(old)
    assert loaded.recovery_policy == 'none' and 'recovery_policy' not in loaded.to_dict()
    assert loaded.to_dict() == old and digest(loaded.to_dict()) == fingerprint
    old.pop('budget_policy')
    assert RunConfig.from_frozen_dict(old).to_dict() == old


@pytest.mark.parametrize('value',['',None,True,[],{},'automatic','exclusive'])
def test_invalid_recovery_policy_is_rejected(value):
    doc = document(); doc['run'] = {'recovery_policy': value}
    with pytest.raises(ValueError, match='recovery_policy'):
        RunConfig.from_dict(doc)


def test_exclusive_recovery_requires_local_actual_policy_and_cli_assertion(tmp_path, monkeypatch):
    doc = document(); doc['run'] = {'recovery_policy':'exclusive-key-v1','budget_policy':'provider-key-v1'}
    with pytest.raises(ValueError, match='local-actual-cost'):
        RunConfig.from_dict(doc)
    captured = []
    monkeypatch.setattr(RunConfig, 'load', lambda path, **kwargs: captured.append(kwargs) or 'frozen')
    assert cli._load(Namespace(config=tmp_path/'run.toml',exclusive_run_key=True)) == 'frozen'
    assert captured[0]['recovery_policy'] == 'exclusive-key-v1'


@pytest.mark.parametrize('change',[
    {'recovery_policy':'generation-v1'}, {'recovery_policy':'none'}, {'active_requests':1},
    {'blocking_unknown_requests':1}, {'provisional_unknown_requests':0},
    {'provisional_unknown_requests':2}, {'provisional_unknown_requests':True},
])
def test_unknown_gate_accepts_only_explicit_validated_exclusive_provisional_counts(change):
    budget={'unknown_requests':1,'active_requests':0,'blocking_unknown_requests':0,
        'provisional_unknown_requests':1,'recovery_policy':'exclusive-key-v1','spent_usd':'1'}
    assert not blocking_unknown_usage(budget)
    assert COST_SPEC.pass_exclusion(budget) is None
    assert blocking_unknown_usage({**budget,**change})
    assert COST_SPEC.pass_exclusion({**budget,**change}) == 'unknown_usage'


def test_historical_unknown_nonblocking_marker_does_not_relax_gate():
    budget={'unknown_requests':1,'active_requests':0,'spent_usd':'1','unreported_cost_nonblocking':True}
    assert blocking_unknown_usage(budget)
    assert COST_SPEC.pass_exclusion(budget) == 'unknown_usage'


def test_product_passes_frozen_recovery_policy_into_relay(cell, monkeypatch):
    from harness import openrouter
    original = openrouter.OpenRouterRelay
    cell.snapshot['config']['recovery_policy']='generation-v1'
    seen = []
    def relay(*args, **kwargs):
        seen.append(kwargs['recovery_policy'])
        return original(*args, **kwargs)
    monkeypatch.setattr(openrouter, 'OpenRouterRelay', relay)
    def execute(config, root, capsule, relay, state):
        charge(relay,state['pass_number'])
        outcome={'status':'completed','native_status':'completed','returncode':0}
        runner.write(capsule/'agent-run.json',outcome)
        return outcome
    monkeypatch.setattr(core, 'execute_pass', execute)
    assert core.run_product(cell.cell,auth_path=cell.auth)==0
    assert seen == ['generation-v1']


def test_known_id_failed_transport_in_same_capsule_resumes_without_resetting_ledger(cell, monkeypatch):
    from harness.openrouter.ledger import read_openrouter_receipt
    cell.snapshot['config']['recovery_policy']='generation-v1'
    cell.config['recovery_policy']='generation-v1'
    runner.write(cell.cell/'config.json',cell.config)
    seen=[]
    def execute(config,root,capsule,relay,state):
        number=state['pass_number'];seen.append(number);relay.set_pass(number)
        request=relay.ledger.reserve(relay.status()['remaining_usd'],pass_number=number)
        relay.ledger.mark_dispatched(request)
        relay.ledger.settle(request,cost_usd='0.5' if number==1 else '2.5',generation_id=f'transport-generation-{number}',
            metadata={'transport_failure':True,'transport_error_category':'timeout'} if number==1 else {})
        outcome={'status':'failed' if number==1 else 'completed','native_status':'failed' if number==1 else 'completed',
            'returncode':1 if number==1 else 0}
        runner.write(capsule/'agent-run.json',outcome);return outcome
    monkeypatch.setattr(core,'execute_pass',execute)
    assert core.run_product(cell.cell,auth_path=cell.auth)==1
    before=read_openrouter_receipt(cell.cell/'billing/openrouter.sqlite')
    assert before['budget']['spent_usd']=='0.5' and before['budget']['active_requests']==0
    assert runner._metering_requeue_ready(cell.snapshot,cell.snapshot['proofs'][0])
    assert core.run_product(cell.cell,auth_path=cell.auth,resume=True)==0
    after=read_openrouter_receipt(cell.cell/'billing/openrouter.sqlite')
    assert seen==[1,2] and after['identity']==before['identity']
    assert after['requests'][0]==before['requests'][0]
    assert Decimal(after['budget']['spent_usd'])==Decimal(after['budget']['limit_usd'])==Decimal('3')
    assert runner.read(cell.cell/'state.json')['passes'][0]['agent_status']=='failed'


@pytest.fixture
def scheduler(tmp_path, monkeypatch):
    root=tmp_path/'run';root.mkdir()
    rows=[{'label':f'proof-{n}','task_id':f'Task{n}','task_sha256':str(n)} for n in range(3)]
    snapshot={'root':str(root),'identity':'fixed','proofs':rows,
        'config':{'concurrency':2,'recovery_policy':'generation-v1','budget_usd':'3'}}
    runner.write(root/'state.json',{'status':'prepared','elapsed_seconds':0})
    monkeypatch.setattr(runner,'load_snapshot',lambda *a,**k:deepcopy(snapshot))
    monkeypatch.setattr(runner,'_credential_arguments',lambda *a:[])
    monkeypatch.setattr(runner,'_metering_requeue_ready',lambda snap,item:item['label']=='proof-0')
    monkeypatch.setattr(runner.process_memory,'capture_process_identity',lambda _:None)
    monkeypatch.setattr(runner.time,'sleep',lambda _:None)
    log=SimpleNamespace(events=[],active=0,peak=0,attempts={},recover_calls=0,duplicate=False,
        raise_recovery=False,raise_initialize=False,revoke_after_success=False,settle_exhausted=False)
    class Process:
        count=0
        def __init__(self,label,argv):
            Process.count+=1;self.pid=10000+Process.count;self.label=label;self.tick=0;self.code=None
            log.attempts[label]=log.attempts.get(label,0)+1
            log.events.append(('spawn',label,'--resume' in argv));log.active+=1;log.peak=max(log.peak,log.active)
        def poll(self):
            self.tick+=1
            if self.tick<2:return None
            if self.code is None:
                failed=self.label=='proof-0' and log.attempts[self.label]==1
                self.code=int(failed);log.active-=1
                cell=root/'proofs'/self.label
                runner.write(cell/'state.json',{'status':'unknown_usage' if failed else 'budget_reached',
                    'budget':{'spent_usd':'0.2' if failed else '3'},'passes':[]})
                runner.write(cell/'best.json',{'score':42,'sha256':self.label})
            return self.code
        def wait(self,*a,**k):return self.code
        def terminate(self):self.code=1
    monkeypatch.setattr(runner.subprocess,'Popen',lambda argv,**k:Process(argv[5],argv))
    class Coordinator:
        def __init__(self,*a,**k):log.events.append(('construct',))
        def initialize(self):
            log.events.append(('initialize',))
            if log.raise_initialize:raise RuntimeError('scripted initialization unavailable')
        def recover(self):
            assert log.active==0
            log.recover_calls+=1;log.events.append(('recover',))
            if log.raise_recovery:raise RuntimeError('scripted provider unavailable')
            if log.settle_exhausted:
                runner.write(root/'proofs/proof-0/state.json',{'status':'budget_reached','budget':{'spent_usd':'3'},'passes':[]})
                return []
            if log.revoke_after_success and (root/'durable-requeue-claim').exists():
                runner.write(root/'proofs/proof-0/state.json',{'status':'unknown_usage','passes':[]})
                return []
            unresolved=runner.read(root/'proofs/proof-0/state.json')['status']=='unknown_usage'
            if log.duplicate or (unresolved and not (root/'durable-requeue-claim').exists()):
                (root/'durable-requeue-claim').write_text('proof-0 claimed once')
                return ['proof-0']
            return []
    module=ModuleType('harness.recovery');module.RecoveryCoordinator=Coordinator
    monkeypatch.setitem(sys.modules,'harness.recovery',module)
    return SimpleNamespace(root=root,snapshot=snapshot,log=log)


def test_scheduler_waits_until_idle_and_requeues_once_with_same_capacity(scheduler):
    s=scheduler
    assert runner.run(s.root,api_key_file=s.root/'host-only-key')==0
    assert s.log.peak==2 and s.log.active==0
    assert s.log.events[1]==('initialize',)
    spawned=[e for e in s.log.events if e[0]=='spawn']
    assert spawned==[('spawn','proof-0',False),('spawn','proof-1',False),('spawn','proof-2',False),('spawn','proof-0',True)]
    assert s.log.recover_calls==2
    state=runner.read(s.root/'state.json')
    assert state['status']=='completed' and state['automatic_requeues']==['proof-0']
    assert state['worker_returncodes']=={'proof-0':0,'proof-1':0,'proof-2':0}
    before=deepcopy(s.log.attempts)
    assert runner.run(s.root,api_key_file=s.root/'host-only-key',resume=True)==0
    assert s.log.attempts==before  # Durable coordinator claim survives invocations.


@pytest.mark.parametrize('failure',['duplicate','provider_error','ineligible'])
def test_scheduler_fails_closed_without_another_retry_loop(scheduler,monkeypatch,failure):
    s=scheduler
    if failure=='duplicate':s.log.duplicate=True
    elif failure=='provider_error':s.log.raise_recovery=True
    else:monkeypatch.setattr(runner,'_metering_requeue_ready',lambda *_:False)
    assert runner.run(s.root,api_key_file=s.root/'host-only-key')==1
    state=runner.read(s.root/'state.json')
    assert state['status']=='needs_attention' and state['recovery_error']['type']=='RuntimeError'
    assert s.log.attempts['proof-0'] <= 2 and s.log.peak <= 2


@pytest.mark.parametrize('mode',['none','legacy_keys'])
def test_none_and_legacy_key_store_never_construct_recovery_coordinator(scheduler,mode):
    s=scheduler
    if mode=='none':s.snapshot['config']['recovery_policy']='none'
    args={'api_key_file':s.root/'key'} if mode=='none' else {'key_store':s.root/'legacy-store'}
    assert runner.run(s.root,**args)==1
    assert not any(e[0]=='construct' for e in s.log.events)


@pytest.mark.parametrize('stage',['initialize','recover'])
def test_successful_manual_resume_clears_prior_recovery_failure(scheduler,stage):
    s=scheduler
    flag='raise_initialize' if stage=='initialize' else 'raise_recovery'
    setattr(s.log,flag,True)
    assert runner.run(s.root,api_key_file=s.root/'key')==1
    assert runner.read(s.root/'state.json')['recovery_error']
    setattr(s.log,flag,False)
    assert runner.run(s.root,api_key_file=s.root/'key',resume=True)==0
    state=runner.read(s.root/'state.json')
    assert state['status']=='completed' and 'recovery_error' not in state


def test_final_provisional_revocation_is_not_hidden_by_successful_worker_codes(scheduler):
    s=scheduler;s.log.revoke_after_success=True
    assert runner.run(s.root,api_key_file=s.root/'key')==1
    state=runner.read(s.root/'state.json')
    assert state['status']=='needs_attention'
    assert set(state['worker_returncodes'].values())=={0}
    assert runner.read(s.root/'results.json')['proofs']['proof-0']['status']=='unknown_usage'


def test_reconciliation_exhausting_allowance_completes_without_a_useless_worker(scheduler):
    s=scheduler;s.log.settle_exhausted=True
    assert runner.run(s.root,api_key_file=s.root/'key')==0
    state=runner.read(s.root/'state.json')
    assert state['status']=='completed' and state['worker_returncodes']['proof-0']==1
    assert s.log.attempts['proof-0']==1 and len(s.log.attempts)==3
    assert 'automatic_requeues' not in state


def test_requeue_requires_healthy_same_pass_transport_failure_and_same_allowance(tmp_path,monkeypatch):
    from harness.openrouter import ledger
    root=tmp_path/'run';cell=root/'proofs/tiny';cell.mkdir(parents=True)
    item={'label':'tiny','task_id':'Tiny','task_sha256':'same-row'}
    snapshot={'root':str(root),'identity':'frozen','config':{'budget_usd':'2.90','recovery_policy':'generation-v1'},'proofs':[item]}
    state={'status':'failed','pass_number':2,'passes':[{'pass_number':2,'validation_healthy':True}]}
    runner.write(cell/'state.json',state)
    receipt={'identity':{'proof_id':runner.proof_identity(snapshot,item),'limit_usd':'2.90'},
        'budget':{'spent_usd':'1','remaining_usd':'1.90','active_requests':0,'unknown_requests':0},
        'requests':[{'pass_number':2,'metadata':{'transport_failure':True,'transport_error_category':'timeout'}}]}
    monkeypatch.setattr(ledger,'read_openrouter_receipt',lambda _:deepcopy(receipt))
    assert runner._metering_requeue_ready(snapshot,item)
    for change in ['other_pass','protocol_conflict','native_only','cap','unhealthy']:
        saved=deepcopy(receipt);saved_state=deepcopy(state)
        if change=='other_pass':receipt['requests'][0]['pass_number']=1
        elif change=='protocol_conflict':receipt['requests'][0]['metadata']['protocol_conflict']=True
        elif change=='native_only':receipt['requests'][0]['metadata'].clear()
        elif change=='cap':receipt['identity']['limit_usd']='3'
        else:state['passes'][0]['validation_healthy']=False;runner.write(cell/'state.json',state)
        assert not runner._metering_requeue_ready(snapshot,item)
        receipt.clear();receipt.update(saved);state.clear();state.update(saved_state);runner.write(cell/'state.json',state)
    receipt['requests'].append({'pass_number':2,'metadata':{}})
    assert not runner._metering_requeue_ready(snapshot,item)  # Earlier transport failure does not excuse later native failure.
