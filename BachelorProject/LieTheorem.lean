import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Weights.Linear

set_option autoImplicit false

open LieAlgebra


-- let k be a field of characteristic zero
variable {k : Type*} [Field k] [CharZero k]
-- Let L be a Lie algebra over k
variable {L : Type*} [LieRing L] [LieAlgebra k L]
-- and let V be a finite-dimensional triangularizable k-representation of L
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
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

open FiniteDimensional

section

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (v : V) (f : Module.End F V)

abbrev preU (n : ℕ) : Submodule F V := Submodule.span F {v' : V | ∃ a < n, v' = f^[n] v}

theorem preU_mono {a b : ℕ} (hab : a ≤ b) : preU v f a ≤ preU v f b := sorry

theorem lemma1 (n : ℕ) : Submodule.map f (preU v f n) ≤ preU v f (n + 1) := sorry

abbrev U : Submodule F V := Submodule.span F (Set.range (fun n ↦ f^[n] v))

theorem exists_basis_iterate : ∃ (k : ℕ) (B : Basis (Fin k) F (U v f)), ∀ i : Fin k, B i = f^[i] v := sorry

end section

variable (A : LieIdeal k L) (χ : Module.Dual k L)


-- We define a submodule of V which is L-invariant
def altWeightSpace : Submodule k V where
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

variable (k V)

abbrev π (z : L) : Module.End k V := LieModule.toEndomorphism k L V z

variable {k V}


theorem lemma2 (z : L) (v : V) (hv : v ∈ altWeightSpace A χ) (n : ℕ) (w z : L)
    (h : π k V w ((π k V z)^[n] v) - χ w • ((π k V z)^[n] v) ∈ preU v (π k V z) n) :
  π k V w ((π k V z)^[n] v) ∈ preU v (π k V z) (n + 1) := sorry

theorem lemma3 (z : L) {v : V} (hv : v ∈ altWeightSpace A χ) (n : ℕ) :
    ∀ w ∈ A, π k V w ((π k V z)^[n] v) - χ w • ((π k V z)^[n] v) ∈ preU v (π k V z) n := sorry

example (w : L) (v : V): ⁅w, v⁆ = π k V w v := by simp

-- theorem: ∀ n,[w, f^[n]v] - (χ z)f^[n]v ∈ <f^[i] v, i < n>
theorem lie_iterate_upperTriag (v : altWeightSpace A χ) (hv : v ≠ 0) (z : A) (w : L) {k₀ : ℕ}
    (B : Basis (Fin k₀) k (U v.val (LieModule.toEndomorphism k L V w)))
    (hB : ∀ i : Fin k₀, B i = (LieModule.toEndomorphism k L V w)^[i] v.val) (n : ℕ) (hn : n < k₀):
  (⁅z.val, ↑(B ⟨n, hn⟩)⁆ ∈ U v.val (LieModule.toEndomorphism k L V w)) ∧
  (⁅z.val, (B ⟨n, hn⟩).val⁆ - (χ z) • ↑(B ⟨n, hn⟩) ∈
    Submodule.span k {v' : V | ∃ i : Fin k₀, (i < n) ∧ v' = B i}) := by
  let f := LieModule.toEndomorphism k L V w
  induction' n with n ih
  · simp [hB]
    constructor
    · rw [v.prop]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
    · rw [v.prop, sub_self]
  · simp [hB]
    constructor
    · have liewcomm : _ :=
        calc ⁅z.val, (LieModule.toEndomorphism k L V w)^[n] ⁅w, ↑v⁆⁆
          = ⁅z.val, (LieModule.toEndomorphism k L V w)^[n] (LieModule.toEndomorphism k L V w v)⁆ := rfl
        _ = ⁅z.val, (LieModule.toEndomorphism k L V w)^[n.succ] v⁆ := by rw [Function.iterate_succ_apply]
        _ = ⁅z.val, LieModule.toEndomorphism k L V w ((LieModule.toEndomorphism k L V w)^[n] v)⁆ := by rw [Function.iterate_succ_apply']
        _ = ⁅z.val, ⁅w, (LieModule.toEndomorphism k L V w)^[n] v⁆⁆ := rfl
      rw [liewcomm, leibniz_lie]
      apply Submodule.add_mem
      · --have hzw : ∀ x : altWeightSpace A χ, ⁅⁅z.val, w⁆, x.val⁆ = χ ⁅z.val, w⁆ • x.val := x.prop ⟨⁅z.val, w⁆, lie_mem_left k L A z.val w z.prop⟩
        --rw [v.prop ⟨⁅z.val, w⁆, lie_mem_left k L A z.val w z.prop⟩]

        sorry
      sorry
    sorry


-- theorem lie_iterate_stable (v : V) (hv : v ∈ altWeightSpace A χ) (hv : v ≠ 0) (z : A) (w : L) :
--   ∀ x ∈ U (↑v) ((LieModule.toEndomorphism k L V) w),
--   ((LieModule.toEndomorphism k L V) ↑z) x ∈ U (↑v) ((LieModule.toEndomorphism k L V) w) := by
--   intro x hx
--   rcases exists_basis_iterate k V v (LieModule.toEndomorphism k L V w) with ⟨k₀, B, hB⟩
--   simp
--   rcases (Basis.mem_submodule_iff B).mp hx with ⟨c, hc⟩
--   have hbasismem : ∀ (i : Fin k₀), (B i).val ∈ U (↑v) ((LieModule.toEndomorphism k L V) w) := by
--     intro i
--     rw [hB i]
--     dsimp [U]
--     apply Submodule.subset_span
--     use i
--   rw [hc]
--   have h' : LieModule.toEndomorphism k L V z.val (Finsupp.sum c fun i x => x • ↑(B i)) =
--       Finsupp.sum c fun i x => LieModule.toEndomorphism k L V z.val (x • ↑(B i)) := by
--     apply map_finsupp_sum (LieModule.toEndomorphism k L V z.val) c
--   dsimp at h'
--   rw [h']
--   apply Submodule.finsupp_sum_mem
--   intro i hi
--   rw [lie_smul]
--   apply Submodule.smul_mem
--   rw [hB i]
--   sorry


-- theorem weight_lie_eq_zero (v : V) (hv :v ∈ altWeightSpace A χ) (hv : v ≠ 0 ) (z : A) (w : L) : χ ⁅z, w⁆ = 0 := by
--   rcases exists_basis_iterate k V v (LieModule.toEndomorphism k L V w) with ⟨k₀, B, hB⟩
--   suffices hbi : ∀ i : Fin k₀, B.repr (B i) i = χ z by
--     have lie_stable : ∀ x ∈ U (↑v) ((LieModule.toEndomorphism k L V) w),
--         ((LieModule.toEndomorphism k L V) ↑z) x ∈ U (↑v) ((LieModule.toEndomorphism k L V) w) := by
--       intro x hx
--       simp

--       sorry
--     have hTr : Matrix.trace (LinearMap.toMatrix B B
--         ((LieModule.toEndomorphism k L V z).restrict lie_stable)) = k₀* (χ z) := by

--       sorry

--     sorry

--   sorry

-- theorem altWeightSpace_lie_stable:
--   ∀ (w : L) (v : V), v ∈ altWeightSpace A χ → ⁅w, v⁆ ∈ altWeightSpace A χ := by
--   intro w v hv z
--   by_cases hv' : v = 0
--   · simp [hv']
--   · have hzwv : ⁅⁅z.val, w⁆, v⁆ = χ ⁅z, w⁆ • v := hv ⟨⁅z,w⁆, lie_mem_left k L A z.val w z.prop⟩
--     rw [leibniz_lie, hv z, hzwv, weight_lie_eq_zero k L V A χ ⟨v, hv⟩ (Subtype.ne_of_val_ne hv') z w, lie_smul,
--     zero_smul, zero_add]



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
