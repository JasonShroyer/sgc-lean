#!/usr/bin/env python3
"""
SGC Universal Data Loader
=========================
Converts any supported format into the canonical (T, D) state vector array
for SGCRelationalEngine. Auto-detects format from file extension.

Supported formats:
  A — CSV (.csv) with header row
  B — NumPy (.npy, .npz)
  C — JSON (.json) array of dicts
  D — Plain text (.txt, .dat) whitespace-separated
"""
import numpy as np
import os, json
from dataclasses import dataclass, field
from typing import List, Optional, Tuple


@dataclass
class DataMetadata:
    """Metadata about the loaded dataset, for report generation."""
    source_path: str
    source_format: str
    columns: List[str]
    means: List[float]
    stds: List[float]
    T: int
    D: int


def load_data(path: str, columns: Optional[List[str]] = None,
              npz_key: Optional[str] = None,
              has_header: bool = True) -> Tuple[np.ndarray, DataMetadata]:
    """
    Load data from any supported format into a normalized (T, D) array.

    Args:
        path: Path to the data file.
        columns: Optional list of column names to select (CSV/JSON only).
        npz_key: Key to use for .npz files.
        has_header: Whether text/CSV files have a header row.

    Returns:
        (data, metadata) where data is (T, D) normalized to zero mean, unit variance.

    Raises:
        ValueError: If T < 30 or D < 2.
        FileNotFoundError: If path does not exist.
    """
    if not os.path.exists(path):
        raise FileNotFoundError(f"Data file not found: {path}")

    ext = os.path.splitext(path)[1].lower()

    if ext == '.csv':
        data, col_names = _load_csv(path, columns)
        fmt = 'csv'
    elif ext == '.npy':
        data, col_names = _load_npy(path)
        fmt = 'npy'
    elif ext == '.npz':
        data, col_names = _load_npz(path, npz_key)
        fmt = 'npz'
    elif ext == '.json':
        data, col_names = _load_json(path, columns)
        fmt = 'json'
    elif ext in ('.txt', '.dat'):
        data, col_names = _load_txt(path, has_header=False)
        fmt = 'txt'
    else:
        raise ValueError(f"Unsupported file format: {ext}")

    T, D = data.shape

    if T < 30:
        raise ValueError(f"Insufficient data: T={T} < 30 minimum. "
                         f"Need at least 30 timesteps for reliable crystallization.")
    if D < 2:
        raise ValueError(f"Insufficient dimensions: D={D} < 2 minimum. "
                         f"Need at least 2 state dimensions to discover structure.")

    # Normalize: zero mean, unit variance per dimension
    means = data.mean(axis=0).tolist()
    stds = data.std(axis=0).tolist()
    for d in range(D):
        if stds[d] < 1e-12:
            stds[d] = 1.0  # constant column — don't divide by zero
    data_norm = (data - np.array(means)) / np.array(stds)

    if columns is not None and col_names != columns:
        col_names = columns if columns else col_names

    meta = DataMetadata(
        source_path=path,
        source_format=fmt,
        columns=col_names,
        means=means,
        stds=stds,
        T=T,
        D=D,
    )

    return data_norm, meta


def _load_csv(path: str, columns: Optional[List[str]] = None
              ) -> Tuple[np.ndarray, List[str]]:
    """Load CSV with header row."""
    import csv
    with open(path, 'r') as f:
        reader = csv.reader(f)
        header = next(reader)
        header = [h.strip() for h in header]

        if columns:
            col_idx = [header.index(c) for c in columns]
            col_names = columns
        else:
            col_idx = list(range(len(header)))
            col_names = header

        rows = []
        for row in reader:
            try:
                rows.append([float(row[i]) for i in col_idx])
            except (ValueError, IndexError):
                continue

    return np.array(rows, dtype=np.float64), col_names


def _load_npy(path: str) -> Tuple[np.ndarray, List[str]]:
    """Load .npy file."""
    arr = np.load(path).astype(np.float64)
    if arr.ndim == 1:
        arr = arr.reshape(-1, 1)
    col_names = [f'dim_{i}' for i in range(arr.shape[1])]
    return arr, col_names


def _load_npz(path: str, key: Optional[str] = None) -> Tuple[np.ndarray, List[str]]:
    """Load .npz file with optional key selection."""
    npz = np.load(path)
    if key:
        arr = npz[key].astype(np.float64)
    else:
        # Use the first array
        first_key = list(npz.keys())[0]
        arr = npz[first_key].astype(np.float64)
    if arr.ndim == 1:
        arr = arr.reshape(-1, 1)
    col_names = [f'dim_{i}' for i in range(arr.shape[1])]
    return arr, col_names


def _load_json(path: str, columns: Optional[List[str]] = None
               ) -> Tuple[np.ndarray, List[str]]:
    """Load JSON array of dicts."""
    with open(path, 'r') as f:
        records = json.load(f)

    if not isinstance(records, list) or len(records) == 0:
        raise ValueError("JSON file must contain a non-empty array of objects")

    if columns:
        col_names = columns
    else:
        col_names = list(records[0].keys())

    rows = []
    for rec in records:
        try:
            rows.append([float(rec[c]) for c in col_names])
        except (KeyError, ValueError):
            continue

    return np.array(rows, dtype=np.float64), col_names


def _load_txt(path: str, has_header: bool = False) -> Tuple[np.ndarray, List[str]]:
    """Load plain text, whitespace-separated."""
    rows = []
    col_names = None
    with open(path, 'r') as f:
        for i, line in enumerate(f):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            if i == 0 and has_header:
                col_names = parts
                continue
            try:
                rows.append([float(x) for x in parts])
            except ValueError:
                if i == 0:
                    col_names = parts
                continue

    arr = np.array(rows, dtype=np.float64)
    if col_names is None:
        col_names = [f'dim_{i}' for i in range(arr.shape[1])]
    return arr, col_names
