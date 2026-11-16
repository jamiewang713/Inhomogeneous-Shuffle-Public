"""Locations of the current sources corresponding to the archived measurement paths."""
from pathlib import Path

EVIDENCE = Path(__file__).resolve().parent
REPOSITORY = EVIDENCE.parents[1]
PROJECTS = REPOSITORY / 'lean-projects'
PROBES = PROJECTS / 'audits' / EVIDENCE.name
