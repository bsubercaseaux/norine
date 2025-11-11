# Commands for Reproducing Results

We use the Python 3 script `enc/norine_general_pysat.py` to create SAT encodings.  
The generated formula can either be printed to a file or solved directly using an internal SAT solver.

---

## Proving Conjecture 2

To verify **Conjecture 2** from our submitted paper, use the following command:

```bash
python3 enc/norine_general_pysat.py -n N --conjecture1 --antipodal-coloring --first-vertex-min-degree
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

Similarly, we can prove Conjecture 4 for $n=7$

```bash
python3 enc/norine_general_pysat.py -n 7 --conjecture2 --first-vertex-min-degree
```


---

## Computing the $f$ and $\hat{f}$ Values

To compute the **$f$ values**, run:

```bash
python3 enc/norine_general_pysat.py -n N -b B --first-vertex-min-degree
```

- Here $B = \alpha \cdot 2^{N-1}$, where $\alpha$ is the average number of color changes, and $2^{N-1}$ is the number of antipodal vertex pairs.

To compute **$\hat{f}$ values**, add the `-p` flag:

```bash
python3 enc/norine_general_pysat.py -n N -b B -p --first-vertex-min-degree
```

For example, the two encodings required to compute $\hat{f}$ for `n = 6` are:

```bash
python3 enc/norine_general_pysat.py -n 6 -b 28 --first-vertex-min-degree
python3 enc/norine_general_pysat.py -n 6 -b 29 --first-vertex-min-degree
```


## Details for reproducibility

We used `kissat` version 4.0.2, and `cadical`  version 2.0.0. The cubing tool `march_cu` is available at [https://github.com/marijnheule/CnC/tree/master/march_cu](https://github.com/marijnheule/CnC/tree/master/march_cu), and `proofix` is available at [https://github.com/zaxioms0/proofix][https://github.com/zaxioms0/proofix].

For example, to cube a formula using `march_cu` using depth 12 (resulting in ~4000 cubes), run

```bash
march_cu <formula>.cnf -q -d 12 -cnf > output.icnf
```
Then, `output.icnf` will contain all the cubes at the end of the formula. We can then split `output.icnf` into as many formulas as cubes it has as follows:
to construct the formula corresponding to the $i$-th cube, copy all the lines of `output.icnf` corresponding to clauses (i.e., lines that start with a number), and then take the $i$-th line starting with `a`, which will look like
```
a <lit 1> <lit 2> .... <lit k> 0
```
and add $k$ unit clauses to the formula
```
<lit 1> 0
<lit 2> 0
...
<lit k> 0
```
