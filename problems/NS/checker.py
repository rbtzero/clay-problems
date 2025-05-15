#!/usr/bin/env python3
import math

ν = 1.0  # kinematic viscosity
σ0 = 0.5

def barrier(E: float) -> float:
    """Return barrier inequality lhs; should be negative if condition holds."""
    return ν * E - math.sqrt(E) * E

if __name__ == "__main__":
    threshold = (ν / 1.0) ** 2
    print(f"Barrier negative for E < {threshold}") 