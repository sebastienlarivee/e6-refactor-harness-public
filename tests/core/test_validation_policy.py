from __future__ import annotations
import pytest
from lean_tools.validation_policy import OriginalDenominatorScorePolicy

def test_original_denominators_define_the_score_and_optimistic_bound() -> None:
    policy = OriginalDenominatorScorePolicy(original_tokens=100, original_heartbeats=1000)
    incumbent = policy.score(tokens=40, heartbeats=200, compatibility_pct=100)
    assert incumbent == 80.0
    assert policy.optimistic_score(tokens=60) == incumbent

def test_component_rounding_matches_the_fixed_score() -> None:
    policy = OriginalDenominatorScorePolicy(original_tokens=100000, original_heartbeats=1000)
    incumbent = policy.score(tokens=40000, heartbeats=200, compatibility_pct=100)
    assert policy.optimistic_score(tokens=60001) == incumbent

def test_bound_exceeds_every_score_in_finite_heartbeat_compatibility_grid() -> None:
    policy = OriginalDenominatorScorePolicy(original_tokens=37, original_heartbeats=91)
    for tokens in (0, 5, 37, 75, 200):
        bound = policy.optimistic_score(tokens=tokens)
        for heartbeats in (0, 1, 91, 500):
            for compatibility in (0, 100 / 3, 200 / 3, 100):
                score = policy.score(tokens=tokens, heartbeats=heartbeats, compatibility_pct=compatibility)
                assert score <= bound

@pytest.mark.parametrize('tokens,heartbeats', [(0, 1), (1, 0), (-1, 1), (True, 1)])
def test_bound_requires_explicit_positive_original_denominators(tokens, heartbeats) -> None:
    with pytest.raises(ValueError):
        OriginalDenominatorScorePolicy(tokens, heartbeats)



def test_rounded_equal_bound_remains_eligible_for_tie_break() -> None:
    policy = OriginalDenominatorScorePolicy(100000, 1000)
    incumbent = policy.score(tokens=40000, heartbeats=200, compatibility_pct=100)
    assert policy.optimistic_score(tokens=60001) == incumbent
    assert not policy.cannot_beat_validated_incumbent(
        tokens=60001, validated_incumbent_score=incumbent,
    )
    assert policy.cannot_beat_validated_incumbent(
        tokens=60006, validated_incumbent_score=incumbent,
    )
