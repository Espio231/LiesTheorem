import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.LinearAlgebra.Dual

open LieAlgebra

-- let k be a field of characteristic zero
variable (k : Type*) [Field k] [CharZero k]
-- Let L be a Lie algebra over k
variable (L : Type*) [LieRing L] [LieAlgebra k L]
-- and let V be a finite-dimensional triangularizable k-representation of L
variable (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [LieRingModule L V] [LieModule k L V] [LieModule.IsTriangularizable k L V] [Nontrivial V]

-- If `L` is nilpotent, we can find a non-zero eigenvector
theorem LieModule.exists_forall_lie_eq_smul' [LieAlgebra.IsNilpotent k L] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  suffices ∃ χ : L → k, weightSpace V χ ≠ ⊥ by
    obtain ⟨χ, hχ⟩ := this
    let χ' : weight k L V := ⟨χ, (finite_weightSpace_ne_bot k L V).mem_toFinset.mpr hχ⟩
    use weight.toLinear k L V χ'
    exact exists_forall_lie_eq_smul_of_weightSpace_ne_bot k L V χ hχ
  by_contra! contra
  simpa [contra] using iSup_weightSpace_eq_top k L V

-- We define a submodule of V which is L-invariant
def altWeightSpace (A : LieIdeal k L) (χ : Module.Dual k L) : Submodule k V where
  carrier := {v |∀ a : A, ⁅a.val,v⁆ = (χ a)•v}
  add_mem' := by
    intro _ _ ha hb x
    rw [lie_add, ha x, hb x, ← smul_add]
  zero_mem' := by
    intro a
    rw [lie_zero, smul_zero]
  smul_mem' := by
    intro c x hx a
    rw [lie_smul, hx, smul_comm]

open FiniteDimensional


-- But a better result, **Lie's theorem**, is true, namely:
-- If `L` is solvable, we can find a non-zero eigenvector
theorem LieModule.exists_forall_lie_eq_smul (h : derivedSeries k L 1 ≠ ⊤ ∨ ⊤ = (⊥ : LieIdeal k L)) :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  sorry

lemma LieModule.exists_forall_lie_eq_smul'' (g : LieSubalgebra k (Module.End k V)) {n : ℕ}
  (hn : finrank k g = n) (hg : g = ⊥ ∨ derivedSeries k g 1 ≠ ⊤) :
  ∃ χ : Module.Dual k g, ∃ v : V, v ≠ 0 ∧ ∀ x : g, ⁅x, v⁆ = χ x • v := by
  revert g
  induction' n with n ih
  · intro g hn _
    use 0
    rcases (exists_ne (0 : V)) with ⟨v, hv⟩
    use v, hv
    intro x
    have xzero : x.val = 0 := by
      exact (Submodule.eq_bot_iff g.toSubmodule).mp (Submodule.finrank_eq_zero.mp hn) x (Submodule.coe_mem x)
    simp [xzero]
  · intro g hn hg
    have hA : ∃ (A : LieIdeal k g), finrank k A = n := by sorry
    rcases hA with ⟨A, hA⟩
    have hz : ∃ (z : g), A.toSubmodule ⊔ (Submodule.span k {z}) = ⊤ := by sorry
    rcases hz with ⟨z, hz⟩
    let A' : LieSubalgebra k (Module.End k V) := LieSubalgebra.map (LieSubalgebra.incl g) A
