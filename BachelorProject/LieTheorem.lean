import Mathlib.Algebra.Lie.Solvable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Lie.Classical


variable {R L n : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

def upperTriagModule [Fintype n] [LinearOrder n] : Submodule R (Matrix n n R) where
  carrier := {m | ∀ i j : n, j < i → m i j = 0}
  add_mem' := by
    intro a b ha hb i j hji
    rw [Matrix.add_apply, ha i j hji, hb i j hji, add_zero]
  zero_mem' := fun _ _ _ ↦ Matrix.zero_apply _ _
  smul_mem' := by
    intro α m hm i j hji
    rw [Matrix.smul_apply, hm i j hji, smul_zero]



def upperTriag [Fintype n] [LinearOrder n] : LieSubalgebra R (Matrix n n R) :=
  {upperTriagModule with
    lie_mem' := sorry}

--
