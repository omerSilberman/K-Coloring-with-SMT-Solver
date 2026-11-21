#!/bin/bash
#SBATCH --job-name=gen-smt2
#SBATCH --partition=p_zohar
#SBATCH --cpus-per-task=4
#SBATCH --mem=64G
#SBATCH --time=12:00:00
#SBATCH --output=gen-smt2-%j.log

# Runs cluster/gen_smt2.py as a Slurm job. Submit it from the project folder, with any
# gen_smt2.py options after it:
#   sbatch cluster/gen_smt2.sbatch
#   sbatch cluster/gen_smt2.sbatch --k-offset -1
# One file at a time per CPU. The largest graphs need up to about 8 GB per file
# (BOOL-DIRECT), hence 64 GB for 4. If the job is stopped, submitting it again keeps the
# files already written.
set -euo pipefail

cd "$SLURM_SUBMIT_DIR"
python3 -u cluster/gen_smt2.py --jobs "${SLURM_CPUS_PER_TASK:-4}" "$@"
