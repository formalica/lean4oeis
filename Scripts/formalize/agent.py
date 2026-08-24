"""pydantic-ai agent wiring. The agent gets no tools on purpose: Lean is always compiled by
the pipeline, so letting the model decide whether to compile would only burn tokens."""

from __future__ import annotations

import json

from pydantic_ai import Agent
from pydantic_ai.messages import ModelMessage, ModelMessagesTypeAdapter
from pydantic_ai.models import Model, infer_model
from pydantic_ai.models.openai import OpenAIChatModel
from pydantic_ai.providers.openai import OpenAIProvider

from .config import Config
from .models import BatchResult, SkillSuggestions

SYSTEM_PROMPT = (
    "You translate OEIS program blocks into Lean 4 + Mathlib. Follow the skill document "
    "you are given exactly. Never invent OEIS data. Prefer a correct, executable, total "
    "definition over a clever one. Answer only with the structured output."
)


def build_model(cfg: Config) -> Model:
    """`provider:model` picks any pydantic-ai provider; a bare name uses the
    OpenAI-compatible endpoint configured by `OEIS_LLM_BASE_URL` / `OEIS_LLM_API_KEY`."""
    if ":" in cfg.model_name:
        return infer_model(cfg.model_name)
    provider = OpenAIProvider(base_url=cfg.base_url, api_key=cfg.api_key)
    return OpenAIChatModel(cfg.model_name, provider=provider)


def build_agent(cfg: Config, skill_text: str) -> Agent[None, BatchResult]:
    return Agent(
        build_model(cfg),
        output_type=BatchResult,
        system_prompt=(SYSTEM_PROMPT, skill_text),
        retries=2,
    )


def build_learning_agent(cfg: Config) -> Agent[None, SkillSuggestions]:
    return Agent(
        build_model(cfg),
        output_type=SkillSuggestions,
        system_prompt=(
            "You maintain a Maple-to-Lean-4 translation skill document. Propose only "
            "generally reusable additions that are not already covered. Return empty lists "
            "when nothing new was learned."
        ),
    )


def dump_history(messages: list[ModelMessage]) -> str:
    return ModelMessagesTypeAdapter.dump_json(messages).decode("utf-8")


def load_history(blob: str) -> list[ModelMessage]:
    if not blob or blob.strip() in ("", "[]"):
        return []
    return list(ModelMessagesTypeAdapter.validate_python(json.loads(blob)))
