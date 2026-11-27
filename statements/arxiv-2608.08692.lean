import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A finite-specialisation statement of González D'León–Wachs Conjecture 7.3
Source: arXiv:2608.08692v2, §§5.2–5.3 and §7.
The connected-block recursion is the published Eq. (5.3) (singleton base case).
The degree piece uses Eq. (7.1) together with the published interval factorisation (5.1).
Schur polynomials are defined by their semistandard tableau sum.
No graph class, colour count, or degree is restricted. As the degree 2d Schur
basis stabilises for at least 2d variables, the family of finite statements
represents the infinite-variable conjecture. Applying the recurrence to a
connected block of size s uses fuel at least s: all blocks in a proper connected
partition are nonempty strict subsets. No fuel-zero branch contributes.
The identity for the degree piece is also stated directly in Theorem 7.2's proof.
-/

namespace DeskWeightedBondConj73

open scoped BigOperators
open Finset

abbrev Poly (r : ℕ) := MvPolynomial (Fin r) ℤ

noncomputable section
open Classical

/-- Connectivity of the induced graph, expressed by nontrivial cuts. -/
def connectedOn {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : Prop :=
  U.Nonempty ∧ ∀ S ⊆ U, S.Nonempty → (U \ S).Nonempty →
    ∃ x ∈ S, ∃ y ∈ U \ S, G.Adj x y

/-- Finite connected set partitions of U, including the empty partition of ∅. -/
def bondParts {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    Finset (Finset (Finset (Fin n))) :=
  univ.filter fun p =>
    p.biUnion id = U ∧
    (∀ A ∈ p, connectedOn G A) ∧
    (∀ A ∈ p, ∀ B ∈ p, A ≠ B → Disjoint A B)

def weightMonomial {r : ℕ} (m : Fin r → ℕ) : Poly r :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm m) 1

/-- One monomial for each weak composition of d into r parts. -/
def completeH (r d : ℕ) : Poly r :=
  ∑ m : Fin r → Fin (d+1),
    if ∑ i, (m i : ℕ) = d then weightMonomial (fun i => (m i : ℕ)) else 0

/-- Only evaluated on nonempty connected blocks, with fuel at least the block size.
The fuel-zero branch will not be used in this reading of the recurrence. -/
def connectedMobius {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) :
    ℕ → Finset (Fin n) → Poly r
  | 0, _ => 0
  | fuel+1, S =>
      if S.card ≤ 1 then 1
      else - ∑ p ∈ (bondParts G S).filter (fun p => p.card > 1),
        completeH r (p.card-1) * ∏ B ∈ p, connectedMobius r G fuel B

/-- (7.1) restricted to homogeneous degree d. -/
def psiDegree {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) (d : ℕ) : Poly r :=
  ∑ p ∈ (bondParts G univ).filter (fun p => n-p.card = d),
    ∏ B ∈ p, connectedMobius r G n B

abbrev RowLengths (D : ℕ) := Fin D → Fin (D+1)

def validShape {D : ℕ} (s : RowLengths D) : Prop :=
  Antitone s ∧ ∑ i, (s i : ℕ) = D

abbrev Cells {D : ℕ} (s : RowLengths D) :=
  {c : Fin D × Fin D // (c.2 : ℕ) < (s c.1 : ℕ)}

def semistandard {D r : ℕ} {s : RowLengths D} (T : Cells s → Fin r) : Prop :=
  (∀ a b, a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a ≤ T b) ∧
  (∀ a b, a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)

/-- Schur polynomial, defined by summing tableau weights. Shapes are zero-padded
partitions of D, so all longer-than-r shapes automatically have no tableaux. -/
def schur (r : ℕ) {D : ℕ} (s : RowLengths D) : Poly r :=
  ∑ T : Cells s → Fin r,
    if semistandard T then weightMonomial (fun i => (univ.filter (T · = i)).card) else 0

/-- Existence of an expansion in Schur polynomials with natural coefficients. -/
def schurPositive (r D : ℕ) (P : Poly r) : Prop :=
  ∃ a : RowLengths D → ℕ,
    P = ∑ s : RowLengths D,
      if validShape s then MvPolynomial.C (a s : ℤ) * schur r s else 0

def turan {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) (d : ℕ) : Poly r :=
  (psiDegree r G d)^2 - psiDegree r G (d-1) * psiDegree r G (d+1)

/-- Conjecture 7.3 in all finite colour alphabets. With the usual stable
specialisations, choosing r ≥ 2d recovers the full symmetric-function assertion. -/
def conjecture73 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r d : ℕ),
    0 < r → 0 < d → schurPositive r (2*d) (turan r G d)


end
end DeskWeightedBondConj73

namespace OMA.S_arxiv_2608_08692

/-- González D’León–Wachs Conjecture 7.3. -/
theorem main : DeskWeightedBondConj73.conjecture73 := by
  sorry

end OMA.S_arxiv_2608_08692
