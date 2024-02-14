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


-- We define the Submodules generated by repeatedly applying a linear map `f: V →ₗ[F] V` to a vector `v`
section

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (v : V) (f : Module.End F V)
-- the Submodule generated by `v`, `f v`, `f f v`, ... , `f^[n-1] v`
abbrev preU (n : ℕ) : Submodule F V := Submodule.span F {v' : V | ∃ a < n, v' = (f^a) v}

theorem preU_mono {a b : ℕ} (h : a ≤ b) : preU v f a ≤ preU v f b :=
  Submodule.span_mono (fun _ ⟨c, hc, hw⟩ ↦ ⟨c, lt_of_lt_of_le hc h, hw⟩)

theorem map_preU_le (n : ℕ) : Submodule.map f (preU v f n) ≤ preU v f (n + 1) := by
  rw [Submodule.map_span]
  apply Submodule.span_mono
  intro w ⟨z, ⟨m, hm, hz⟩, hw⟩
  use m + 1, Nat.add_lt_add_right hm 1
  rw [← hw, pow_succ, hz]
  rfl

abbrev U : Submodule F V := Submodule.span F (Set.range (fun (n : ℕ) ↦ (f^n) v))

theorem exists_basis_iterate : ∃ (k : ℕ) (B : Basis (Fin k) F (U v f)), ∀ i : Fin k, B i = (f^i.val) v := sorry

end


section

variable (A : LieIdeal k L) (χ : Module.Dual k L)

variable (k V)
-- the lie action of `L` on `V`
abbrev π (z : L) : Module.End k V := LieModule.toEndomorphism k L V z
variable {k V}

-- We define a submodule of V which is L-invariant
def altWeightSpace : Submodule k V where
  carrier := {v |∀ a ∈ A, ⁅a,v⁆ = (χ a)•v}
  add_mem' := by
    intro _ _ ha hb _ _
    rwa [lie_add, ha, hb, ← smul_add]
    assumption
  zero_mem' := by
    intro _ _
    rw [lie_zero, smul_zero]
  smul_mem' := by
    intro _ _ hx _ _
    rwa [lie_smul, hx, smul_comm]

theorem lemma2 (z w : L) (v : V) (n : ℕ)
    (h : π k V w (((π k V z) ^ n) v) - χ w • (((π k V z)^n) v) ∈ preU v (π k V z) n) :
  π k V w (((π k V z)^n) v) ∈ preU v (π k V z) (n + 1) := by
  let πz : Module.End k V := π k V z
  have t₁ : π k V w ((πz^n) v) =
      (π k V w ((πz^n) v) - χ w • ((πz^n) v) + χ w • ((πz^n) v)) := by simp
  rw [t₁]
  apply Submodule.add_mem
  · apply (preU_mono v πz n.le_succ)
    assumption
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    use n
    simp

example (f g : Module.End k V) (n : ℕ) : Module.End k V := f * g^n

theorem lemma3 (z : L) {v : V} (hv : v ∈ altWeightSpace A χ) (n : ℕ) :
    ∀ w ∈ A, π k V w (((π k V z)^n) v) - χ w • (((π k V z)^n) v) ∈ preU v (π k V z) n := by
  induction' n with n ih
  · intro w hw
    simp [hv w hw]
  · intro w hw
    rw [pow_succ]
    dsimp
    rw [leibniz_lie, ← lie_smul, add_sub_assoc]
    apply Submodule.add_mem
    · exact lemma2 χ z ⁅w,z⁆ v n (ih ⁅w,z⁆ (lie_mem_left k L A w z hw))
    · rw [← lie_sub]
      apply map_preU_le
      use ⁅w, ((π k V z)^n) v⁆ - χ w • (((π k V z)^n) v)
      constructor
      exact ih w hw
      trivial

abbrev T (w : L) : Module.End k V := (π k V w)  - χ w • 1

theorem T_apply_succ (z w : L) (hw : w ∈ A) {v : V} (hv : v ∈ altWeightSpace A χ) (n : ℕ) :
  Submodule.map (T χ w) (preU v (π k V z) (n + 1)) ≤ preU v (π k V z) n:= sorry

theorem altWeightSpace_lie_stable:
  ∀ (w : L) (v : V), v ∈ altWeightSpace A χ → ⁅w, v⁆ ∈ altWeightSpace A χ := by
  intro w v hv z hz
  by_cases hv' : v = 0
  · simp [hv']
  · have hzwv : ⁅⁅z, w⁆, v⁆ = χ ⁅z, w⁆ • v := hv ⁅z,w⁆ (lie_mem_left k L A z w hz)
    rw [leibniz_lie, hv z hz, hzwv]
    sorry

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
