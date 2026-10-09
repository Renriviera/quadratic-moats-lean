#!/usr/bin/env python3
"""Run Lean's endpoint audits and fail on missing or unexpected axiom reports."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDITS = {
    "checkpoints/AuditFinal.lean": {
        "QuadraticMoat.finiteDivisorNoWalkEndpoint_proved",
        "QuadraticMoat.uniformEndpoint_proved",
        "QuadraticMoat.allQuadraticEndpoint_proved",
        "QuadraticMoat.irreducible_components_uniformly_bounded",
    },
    "checkpoints/AuditBoundedFactors.lean": {
        "OAI.GaussianMoat.FinLaw.posterior_soft_information_lower",
        "QuadraticMoat.BoundedFactors.finiteFactorHitCount_le_omega",
        "QuadraticMoat.BoundedFactors.hitMass_sum_le",
        "QuadraticMoat.BoundedFactors.soft_schedule_batch_information",
        "QuadraticMoat.BoundedFactors.certificate_no_walk",
        "QuadraticMoat.BoundedFactors.finiteHitNoWalkEndpoint_proved",
        "QuadraticMoat.BoundedFactors.uniformEndpoint_proved",
        "QuadraticMoat.BoundedFactors.bounded_distinct_factors_components_uniformly_bounded",
    },
}


def validate_report(output, expected):
    reports = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", output)
    seen = set()
    for name, body in reports:
        seen.add(name)
        axioms = {part.strip() for part in body.split(",") if part.strip()}
        unexpected = axioms - ALLOWED
        if unexpected:
            raise ValueError(f"{name}: unexpected axioms: {', '.join(sorted(unexpected))}")
    missing = expected - seen
    if missing:
        raise ValueError(f"Missing axiom reports: {', '.join(sorted(missing))}")


def main():
    for source, expected in AUDITS.items():
        result = subprocess.run(
            [str(ROOT / "lakew"), "env", "lean", source],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(result.stdout, end="", flush=True)
        if result.returncode:
            return result.returncode
        try:
            validate_report(result.stdout, expected)
        except ValueError as error:
            print(error, file=sys.stderr)
            return 1
    print("All 12 required axiom reports passed; only standard Lean axioms are allowed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
