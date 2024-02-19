import Mathlib.RingTheory.Noetherian

theorem IsNilpotent_iff_of_FG (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (f : M →ₗ[R] M) :
  IsNilpotent f ↔ ∀ m : M, ∃ n : ℕ, (f^n) m = 0 := by
  constructor
  · rintro ⟨n, hn⟩ m
    use n
    simp [hn]
  · intro h
    rcases Module.Finite.out (R := R) (M := M) with ⟨S, hS⟩
    choose g hg using h
    use Finset.sup S g
    ext m
    have hm : m ∈ Submodule.span R S := by simp [hS]
    induction' hm using Submodule.span_induction' with x hx
    · have hx' : x ∈ S := hx
      have h' := Finset.le_sup (f := g) hx'
      specialize hg x
      exact LinearMap.pow_map_zero_of_le h' hg
    · simp
    · simp_all
    · simp_all
