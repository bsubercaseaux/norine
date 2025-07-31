# Commands for Reproducing Results

We use the Python script `enc/norine_general_pysat.py` to create SAT encodings.  
The generated formula can either be printed to a file or solved directly using an internal SAT solver.

---

## Proving Conjecture 2

To verify **Conjecture 2** from our submitted paper, use the following command:

```bash
python enc/norine_general_pysat.py -n N --conjecture1 --antipodal-coloring --first-vertex-min-degree
```

- `N` is the number of dimensions.
- To **write the encoding to a file** instead of solving it, add:
  ```bash
  --tmp-file FILE --no-solve
  ```
- By default, paths are restricted to **geodesics**.  
  To allow **general paths**, use the `--path` option.
- To set the **max_comp** parameter for symmetry breaking, use:
  ```bash
  --partial-sym-break VALUE
  ```

Run `--help` for a complete list of available options.

---

## Proving Conjecture 4

Similarly, we can proof Conjecture 4 for $n=7$

```bash
python enc/norine_general_pysat.py -n 7 --conjecture2 --first-vertex-min-degree
```


---

## Computing the $f$ and $\hat{f}$ Values

To compute the **$f$ values**, run:

```bash
python enc/norine_general_pysat.py -n N -b B --first-vertex-min-degree
```

- Here,  
  $$
  B = \alpha \cdot 2^{N-1}
  $$  
  where $\alpha$ is the average number of color swaps, and $2^{N-1}$ is the number of antipodal vertex pairs.

To compute **$\hat{f}$ values**, add the `-p` flag:

```bash
python enc/norine_general_pysat.py -n N -b B -p --first-vertex-min-degree
```

For example, the two encodings required to compute $\hat{f}$ for `n = 6` are:

```bash
python enc/norine_general_pysat.py -n 6 -b 28 --first-vertex-min-degree
python enc/norine_general_pysat.py -n 6 -b 29 --first-vertex-min-degree
```