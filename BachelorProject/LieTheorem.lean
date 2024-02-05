import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Weights.Linear

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

theorem exists_basis_iterate (F V : Type*) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (v : V) (f : V →ₗ[F] V) : ∃ (k : ℕ) (B : Basis (Fin k) F (Submodule.span F (Set.range (fun n ↦ f^[n] v)))),
    ∀ i : Fin k, B i = f^[i] v
    := sorry

theorem altWeightSpace_lie_stable (A : LieIdeal k L) (χ : Module.Dual k L):
  ∀ (z : L) (v : V), v ∈ altWeightSpace k L V A χ → ⁅z, v⁆ ∈ altWeightSpace k L V A χ := sorry

-- theorem: ∀ n,[w, f^[n]v - λv] ∈ <f^[i] v, i < n>

-- But a better result, **Lie's theorem**, is true, namely:
-- If `L` is solvable, we can find a non-zero eigenvector
theorem LieModule.exists_forall_lie_eq_smul [IsSolvable k L] :
    ∃ χ : Module.Dual k L, ∃ v : V, v ≠ 0 ∧ ∀ x : L, ⁅x, v⁆ = χ x • v := by
  sorry

theorem isSolvable_of_le (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] {K K' : LieSubalgebra R L}
    [IsSolvable R K'] (h : K ≤ K') : IsSolvable R K := sorry

lemma LieModule.exists_forall_lie_eq_smul'' (g : LieSubalgebra k (Module.End k V)) {n : ℕ}
  (hn : finrank k g = n) [IsSolvable k g] :
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
    have hA : ∃ (A : LieSubalgebra k (Module.End k V)), (A ≤ g) ∧ (finrank k A = n)
    ∧ (∀ x y : Module.End k V, x ∈ A → y ∈ g → ⁅x,y⁆ ∈ A) := sorry
    rcases hA with ⟨A, hALEg, hdimA, hAgIdeal⟩
    have hz : ∃ (z : g), A.toSubmodule ⊔ (Submodule.span k {z.val}) = g := sorry
    rcases hz with ⟨z, hz⟩
    have h₁ : _ := by
      have : IsSolvable k A := isSolvable_of_le k (Module.End k V) hALEg
      apply ih A hdimA
    rcases h₁ with ⟨χ, v, hv, hweight⟩
    sorry
