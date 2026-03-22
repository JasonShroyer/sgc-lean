#!/usr/bin/env python3
"""Tests for sgc_universal_loader.py — TDD: write tests before implementation."""
import numpy as np
import os, sys, json, tempfile, unittest

sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal_loader import load_data, DataMetadata


class TestUniversalLoader(unittest.TestCase):

    def setUp(self):
        self.tmpdir = tempfile.mkdtemp()

    def _path(self, name):
        return os.path.join(self.tmpdir, name)

    # --- Format A: CSV ---

    def test_csv_basic(self):
        """CSV with header row loads correctly."""
        path = self._path("test.csv")
        with open(path, 'w') as f:
            f.write("x,y,z\n")
            for t in range(50):
                f.write(f"{t*0.1},{np.sin(t*0.1)},{np.cos(t*0.1)}\n")
        data, meta = load_data(path)
        self.assertEqual(data.shape, (50, 3))
        self.assertEqual(meta.columns, ['x', 'y', 'z'])
        self.assertEqual(meta.source_format, 'csv')
        # Normalized: mean ≈ 0, std ≈ 1
        self.assertAlmostEqual(float(np.mean(data[:, 0])), 0.0, places=5)
        self.assertAlmostEqual(float(np.std(data[:, 0])), 1.0, places=5)

    def test_csv_select_columns(self):
        """CSV with column selection."""
        path = self._path("test2.csv")
        with open(path, 'w') as f:
            f.write("t,x,y,z,junk\n")
            for t in range(40):
                f.write(f"{t},{t*0.1},{np.sin(t*0.1)},{np.cos(t*0.1)},0\n")
        data, meta = load_data(path, columns=['x', 'y', 'z'])
        self.assertEqual(data.shape, (40, 3))
        self.assertEqual(meta.columns, ['x', 'y', 'z'])

    # --- Format B: NumPy ---

    def test_npy(self):
        """NPY file loads correctly."""
        path = self._path("test.npy")
        arr = np.random.randn(100, 4)
        np.save(path, arr)
        data, meta = load_data(path)
        self.assertEqual(data.shape, (100, 4))
        self.assertEqual(meta.source_format, 'npy')

    def test_npz(self):
        """NPZ file with key selection."""
        path = self._path("test.npz")
        arr = np.random.randn(60, 3)
        np.savez(path, states=arr, other=np.zeros(5))
        data, meta = load_data(path, npz_key='states')
        self.assertEqual(data.shape, (60, 3))

    # --- Format C: JSON ---

    def test_json(self):
        """JSON array of dicts."""
        path = self._path("test.json")
        records = [{'x': float(i), 'y': float(i**2), 'z': float(np.sin(i))}
                   for i in range(50)]
        with open(path, 'w') as f:
            json.dump(records, f)
        data, meta = load_data(path, columns=['x', 'y', 'z'])
        self.assertEqual(data.shape, (50, 3))
        self.assertEqual(meta.source_format, 'json')

    # --- Format D: Plain text ---

    def test_txt_whitespace(self):
        """Plain text, whitespace-separated."""
        path = self._path("test.txt")
        with open(path, 'w') as f:
            for t in range(50):
                f.write(f"{t*0.1} {np.sin(t*0.1)} {np.cos(t*0.1)}\n")
        data, meta = load_data(path)
        self.assertEqual(data.shape, (50, 3))
        self.assertEqual(meta.source_format, 'txt')

    # --- Validation ---

    def test_too_few_rows(self):
        """Raise ValueError if T < 30."""
        path = self._path("small.csv")
        with open(path, 'w') as f:
            f.write("x,y\n")
            for t in range(10):
                f.write(f"{t},{t}\n")
        with self.assertRaises(ValueError):
            load_data(path)

    def test_too_few_dims(self):
        """Raise ValueError if D < 2."""
        path = self._path("1d.csv")
        with open(path, 'w') as f:
            f.write("x\n")
            for t in range(50):
                f.write(f"{t}\n")
        with self.assertRaises(ValueError):
            load_data(path)

    # --- Metadata ---

    def test_metadata_normalization_params(self):
        """Metadata records mean and std for denormalization."""
        path = self._path("meta.csv")
        with open(path, 'w') as f:
            f.write("a,b\n")
            for t in range(50):
                f.write(f"{100+t},{200+t*2}\n")
        data, meta = load_data(path)
        self.assertEqual(len(meta.means), 2)
        self.assertEqual(len(meta.stds), 2)
        self.assertAlmostEqual(meta.means[0], 100 + 24.5, places=0)
        self.assertTrue(meta.stds[1] > 0)


if __name__ == '__main__':
    unittest.main()
