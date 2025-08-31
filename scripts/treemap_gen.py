import os
import plotly.express as px
import itertools
from git import Repo
import numpy as np
import pandas as pd
print(os.getcwd())

repo = Repo(".")
physlean_path = os.path.join(repo.working_tree_dir, "PhysLean")
folders = [name for name in os.listdir(physlean_path) if os.path.isdir(os.path.join(physlean_path, name))]
folder_map = {folder: idx + 1 for idx, folder in enumerate(folders)}
print(folder_map)
blobs = [{
    'parent': os.path.dirname(blob.path) or "/",
    'idee': blob.path,
    'labeling': blob.path.rsplit("/", 1)[-1].removesuffix("lean"),
    'size': blob.size,

    #'commits': len(commits := list(repo.iter_commits(paths=blob.path))),
    'value': (
        folder_map.get(blob.path.split("/")[1], 0)
        if len(blob.path.split("/")) > 1 and blob.path.startswith("PhysLean/")
        else 0
    )} for blob in repo.tree().traverse() if "PhysLean" in blob.path.rsplit("/", 1)[0]]

print(blobs[-1])



fig = px.treemap(
blobs,
    names='labeling',
    ids = 'idee',
    parents='parent',
    labels = 'labeling',
    color='value',
    #hover_data=['commits'],
    values='size',

    color_continuous_scale='plasma'
).show()
