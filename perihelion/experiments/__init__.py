"""
Perihelion Experiments: EGI Verification Pipelines
====================================================

Sprint C: Tower validation with full technology stack
Sprint D: Self-reference testing with composite inputs

Author: SGC Research Team
Date: March 31, 2026
"""

from .sprint_c_tower_validation import (
    SprintCConductor,
    TowerResult,
    TaskResult,
    ModularAdditionTask,
    ParityTask,
    PermutationTask,
)

__all__ = [
    'SprintCConductor',
    'TowerResult',
    'TaskResult',
    'ModularAdditionTask',
    'ParityTask',
    'PermutationTask',
]
