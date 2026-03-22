# Symmetry Completion as Section Extension

## The Right Question

From SGC theory, the gauge group G is defined by:
```
σ(g·x) = g·σ(x)  for all g ∈ G
```

But for task 1b60fb0c, no non-trivial G exists where this holds. The section is NOT equivariant.

**The right question**: What if the task's PURPOSE is to CREATE symmetry?

## Two Classes of Tasks

### Class 1: G-Equivariant Tasks (e.g., 0dfd9992)
- Input has symmetry G
- Output has symmetry G  
- The section σ preserves G
- **Perception**: Detect G in input, apply G-equivariant operation

### Class 2: G-Completion Tasks (e.g., 1b60fb0c)
- Input has partial/broken G-symmetry
- Output has full G-symmetry
- The section σ CREATES G-symmetry
- **Perception**: Detect G in output, extend input to achieve G

## Formalizing Class 2: Section Extension

Let G be a group acting on the grid X.

**Definition (G-symmetric subset)**: A subset S ⊆ X is G-symmetric if g·S = S for all g ∈ G.

**Definition (G-kernel)**: For a grid I, the G-kernel is the maximal subset K ⊆ I such that:
- K is G-symmetric
- I restricted to K equals g·I restricted to g·K for all g ∈ G

In other words: K is where the input ALREADY satisfies G-symmetry.

**Definition (G-defect)**: The G-defect D = I \ K. These are pixels that BREAK the G-symmetry.

**Theorem (Unique Extension for Abelian G)**: If G is Abelian, there exists a unique minimal extension E of I such that:
1. E is G-symmetric
2. E agrees with I on the G-kernel K
3. E is obtained by applying all g ∈ G to the defect D

**Proof sketch**: For Abelian G, the group action commutes, so applying all g to D gives a well-defined result. The minimality follows from taking only the orbit of D under G.

## Application to Task 1b60fb0c

Let G = Z_2 (reflection across vertical axis at position a).

**Step 1**: Detect G_target from output
- The output has reflection symmetry at axis a
- This determines G = Z_2 with action r: (i,j) ↦ (i, 2a-j)

**Step 2**: Compute the G-kernel of input
- K = {(i,j) : I[i,j] = I[i, 2a-j] or both are 0}
- These are pixels where input already has reflection symmetry

**Step 3**: Compute the G-defect
- D = {(i,j) : I[i,j] ≠ 0 and I[i, 2a-j] = 0}
- These are "protrusions" - pixels without symmetric partners

**Step 4**: Extend to G-symmetric
- For each (i,j) ∈ D, add pixel at (i, 2a-j)
- The added pixels form the OUTPUT's new content

## Why This is Theory-Driven

The "protrusion" concept now has a precise definition:
> **Protrusion = G-defect = ker(I - g·I) for g ∈ G**

The "body" concept:
> **Body = G-kernel = where input is G-invariant**

The transformation:
> **Output = Input ∪ G·(defect) = minimal G-symmetric extension**

## The Algorithm Emerges

```
function symmetry_completion(input, G_target):
    # G_target detected from output structure
    
    # Compute kernel and defect
    kernel = {x : input[x] = input[g·x] for all g ∈ G_target, or both zero}
    defect = input \ kernel
    
    # Extend by group action
    output = input.copy()
    for x in defect:
        for g in G_target:
            output[g·x] = apply_color_transform(input[x], g)
    
    return output
```

The color transform handles cases where reflection uses a different color (like 1→2 in 1b60fb0c).

## Connection to SGC Theory

This is precisely **section extension** in sheaf theory:
- The input is a section defined on a partial domain
- G-symmetry defines a covering of the full domain
- The task is to extend the section to the full domain
- The extension is unique (for Abelian G) because local sections glue uniquely

The "obstruction to extension" is the holonomy around cycles. For Z_2, there are no non-trivial cycles, so extension always exists.

## Hierarchy of Symmetry Groups

From simplest to most complex:

1. **Translation Z_p × Z_q**: Periodic tiling, detected by FFT
2. **Reflection Z_2**: Mirror symmetry, detected by flip-correlation  
3. **Rotation C_n**: n-fold rotational, detected by rotation-correlation
4. **Dihedral D_n**: Rotation + reflection combined
5. **Permutation S_n**: Color permutations (more complex)

Each has:
- A detection method (spectral for translation, correlation for others)
- A kernel/defect decomposition
- A unique extension (if Abelian) or multiple extensions (if non-Abelian)

## The Perception Layer (Theory-Derived)

The perception layer should:
1. **For each candidate G**: Detect if OUTPUT has G-symmetry
2. **If yes**: Compute G-kernel of INPUT
3. **Verify**: Check if OUTPUT = minimal G-extension of INPUT
4. **If verified**: Return G and the extension operation

This is not empirical pattern matching - it's checking whether the task fits the G-completion schema.
