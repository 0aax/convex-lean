from __future__ import annotations

import tempfile
from pathlib import Path

from harbor.agents.installed.claude_code import ClaudeCode

from claude_code_thinking import ClaudeCodeThinking

def _agent(**kwargs) -> ClaudeCodeThinking:
    return ClaudeCodeThinking(logs_dir=Path(tempfile.mkdtemp()), **kwargs)

def test_thinking_display_reaches_the_command_line() -> None:
    flags = _agent(thinking_display="summarized").build_cli_flags()
    assert "--thinking-display summarized" in flags

def test_inherited_flags_still_work() -> None:
    flags = _agent(
        reasoning_effort="xhigh", thinking_display="summarized"
    ).build_cli_flags()
    assert "--effort xhigh" in flags
    assert "--permission-mode=bypassPermissions" in flags
    assert "--thinking-display summarized" in flags

def test_omitting_it_emits_nothing() -> None:
    assert "--thinking-display" not in _agent().build_cli_flags()

def test_parent_is_not_mutated() -> None:
    assert not any(f.kwarg == "thinking_display" for f in ClaudeCode.CLI_FLAGS)
    assert any(f.kwarg == "thinking_display" for f in ClaudeCodeThinking.CLI_FLAGS)

def test_version_still_carries_the_cli_pin() -> None:
    assert _agent(version="2.1.220").version() == "2.1.220"

def test_name_is_distinct_from_stock() -> None:
    assert ClaudeCodeThinking.name() != ClaudeCode.name()
