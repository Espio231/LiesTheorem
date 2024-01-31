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

-- But a better result, **Lie's theorem**, is true, namely:
-- If `L` is solvable, we can find a non-zero eigenvector
theorem LieModule.exists_forall_lie_eq_smul [IsSolvable k L] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  sorry
