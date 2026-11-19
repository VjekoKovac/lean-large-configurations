# A first Lean session with Theorem 3

For $d=2$, $p=3$, and $n=8$, Theorem 3 gives a measurable planar set of density $5/6$. Its eight-point pattern is absent along a sequence of positive scales tending to infinity. The threshold holds because $2d+1=5$, and the denominator in the density is $8-2\cdot2+2=6$. In this session you specialize the general theorem and check that Lean derives exactly that conclusion.

## Open the project

1. Install VS Code and its **Lean 4** extension. Follow the extension's setup guide to install the toolchain manager. [Official Lean installation guide](https://lean-lang.org/install/)
2. Extract the repository archive. In VS Code choose **File → Open Folder** and open the directory containing `lean-toolchain`, `lakefile.toml`, and `Solution.lean`. The toolchain manager reads the version pin in this directory.
3. Open a terminal in that folder and run the commands below. Lake is Lean's project build tool. The cache command downloads the compiled mathlib dependencies.

```sh
lean --version
lake --version
lake exe cache get
lake build Solution
```

A first build can take time. Open `Solution.lean` after it finishes. Put the cursor on `Density.nonEuclideanLp`, or on `nonEuclideanLp` inside the namespace `Density`. The Lean Infoview displays its type. Use **Go to Definition** on `FullLpStatement` to see its quantifiers. In particular, the witnesses for $E$ and $P$ occur after $n$, and the same witnesses work for every index of the scale sequence.

## Specialize the theorem

Create a scratch file named `FirstSession.lean` beside `Solution.lean`. Paste this entire block.

```lean
module

public import Solution

open Density

#check Density.nonEuclideanLp
#print Density.FullLpStatement

public theorem firstDensityExample :
    ∃ (E : Set (Point 2)) (P : Finset (Point 2)),
      IsObstruction 3 8 E P ∧ HasDensity E (5 / 6) := by
  obtain ⟨E, P, hcopy, hdens⟩ :=
    nonEuclideanLp 2 3 (by norm_num) (by norm_num) (by norm_num) 8 (by norm_num)
  refine ⟨E, P, hcopy, ?_⟩
  convert hdens using 1
  norm_num

#print axioms firstDensityExample
```

`#check` displays the type of the theorem. `#print` unfolds the named definition. The symbol `ℕ` denotes natural numbers, `ℝ` denotes real numbers, and `∃` reads “there exists.” VS Code's Lean extension accepts `\N`, `\R`, and `\exists` as input abbreviations.

Click inside the proof and move the cursor down one tactic at a time.

- After `obtain`, the context contains the witnesses `E` and `P` and the two facts named `hcopy` and `hdens`. The four calls to `norm_num` establish $1≤2$, $1<3$, $3≠2$, and $2\cdot2+1≤8$.
- After `refine`, Lean asks you to show `HasDensity E (5 / 6)`. The term `hcopy` has already supplied the whole obstruction for this same set and pattern, including cardinality and all the missing scales.
- `convert hdens using 1` reduces the remaining goal to equality of the two real numbers in the density formula. `norm_num` generates a proof of that equality which the Lean kernel checks.

Run your scratch file from the terminal.

```sh
lake env lean FirstSession.lean
```

The last line of output for the block above on Lean 4.35.0 was

```text
'firstDensityExample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To trace the geometry, open `Density/FullLp.lean`. Its proof chooses a stripe set, a pattern of size exactly $n$, and explicit forbidden scales. Follow `card_crossPattern` to see why the pattern has the right size, `no_scaled_copy_cross` to see how it excludes every isometric embedding at those scales, and `hasDensity_stripes` to see the Lebesgue-measure calculation. Each name links to the proof of one mathematical assertion in the source.

## Recover Theorem 1 from Theorem 2

In a second scratch file, try the specialization that uses the **uniform even-exponent conclusion**. The hypothesis `h` is the full statement of Theorem 2. The pair `⟨1, rfl⟩` proves that two is even.

```lean
module

import Density.IntegerLp

open Density

#check ActualCase
#print EuclideanStatement

example (h : IntegralLpStatement) : EuclideanStatement := by
  unfold EuclideanStatement
  obtain ⟨C, hC, N, hN⟩ := h.2 2 (by decide) (by exact ⟨1, rfl⟩)
  refine ⟨C, hC, N, ?_⟩
  intro d hd n hn
  simpa only [Nat.cast_ofNat] using hN d hd n hn
```

Move through the proof from `obtain` to `intro`. Lean gives you the constant `C` and the cutoff `N` before you introduce the ambient dimension `d`. At the final line the hypotheses match the even branch of Theorem 2 for that dimension. Every measurable set, pattern, and scale required by `ActualCase` comes with that branch.
