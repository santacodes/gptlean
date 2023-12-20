# INSTALLATION

## REQUIRMENTS

1.Download and install Miniconda Python .
2.Create the conda environment and install Python dependencies:
```
conda create --yes --name ReProver python=3.10 ipython numpy
conda activate ReProver
pip install torch --index-url https://download.pytorch.org/whl/cu121  # Depending on your CUDA version; see https://pytorch.org/.
pip install tqdm loguru deepspeed pytorch-lightning[extra] transformers tensorboard openai rank_bm25 lean-dojo
```
3.Prepend the repo's root to the PYTHONPATH environment variable.
4.Make sure wget and tar are available. Then, run python scripts/download_data.py to download LeanDojo Benchmark and LeanDojo Benchmark 4. They will be saved to ./data.
5.Satisfy the requirements of LeanDojo.
6.Use LeanDojo to trace all repos in the datasets: python scripts/trace_repos.py. This step may take some time. Please refer to LeanDojo's documentation if you encounter any issues.