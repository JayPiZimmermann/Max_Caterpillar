import MaxCaterpillar.Frontier.StarCertificate.XiEvenTargets
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators
def leafPermutationTable : Fin 24 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]
def leafMaskPermutation : Fin 24 → Fin 15 → Fin 15 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 11, 12, 13, 14], ![0, 3, 4, 1, 2, 5, 6, 7, 8, 11, 12, 9, 10, 13, 14], ![0, 3, 4, 7, 8, 11, 12, 1, 2, 5, 6, 9, 10, 13, 14], ![0, 7, 8, 1, 2, 9, 10, 3, 4, 11, 12, 5, 6, 13, 14], ![0, 7, 8, 3, 4, 11, 12, 1, 2, 9, 10, 5, 6, 13, 14], ![1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11, 13, 12, 14], ![1, 0, 2, 7, 9, 8, 10, 3, 5, 4, 6, 11, 13, 12, 14], ![1, 3, 5, 0, 2, 4, 6, 7, 9, 11, 13, 8, 10, 12, 14], ![1, 3, 5, 7, 9, 11, 13, 0, 2, 4, 6, 8, 10, 12, 14], ![1, 7, 9, 0, 2, 8, 10, 3, 5, 11, 13, 4, 6, 12, 14], ![1, 7, 9, 3, 5, 11, 13, 0, 2, 8, 10, 4, 6, 12, 14], ![3, 0, 4, 1, 5, 2, 6, 7, 11, 8, 12, 9, 13, 10, 14], ![3, 0, 4, 7, 11, 8, 12, 1, 5, 2, 6, 9, 13, 10, 14], ![3, 1, 5, 0, 4, 2, 6, 7, 11, 9, 13, 8, 12, 10, 14], ![3, 1, 5, 7, 11, 9, 13, 0, 4, 2, 6, 8, 12, 10, 14], ![3, 7, 11, 0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14], ![3, 7, 11, 1, 5, 9, 13, 0, 4, 8, 12, 2, 6, 10, 14], ![7, 0, 8, 1, 9, 2, 10, 3, 11, 4, 12, 5, 13, 6, 14], ![7, 0, 8, 3, 11, 4, 12, 1, 9, 2, 10, 5, 13, 6, 14], ![7, 1, 9, 0, 8, 2, 10, 3, 11, 5, 13, 4, 12, 6, 14], ![7, 1, 9, 3, 11, 5, 13, 0, 8, 2, 10, 4, 12, 6, 14], ![7, 3, 11, 0, 8, 4, 12, 1, 9, 5, 13, 2, 10, 6, 14], ![7, 3, 11, 1, 9, 5, 13, 0, 8, 4, 12, 2, 10, 6, 14]]

theorem leafPermutationTable_bijective : ∀ p : Fin 24, Function.Bijective (leafPermutationTable p) := by decide

noncomputable def leafPermutationEquiv (p : Fin 24) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (leafPermutationTable p) (leafPermutationTable_bijective p)

@[simp] theorem leafPermutationEquiv_apply (p : Fin 24) (i : Fin 4) :
    leafPermutationEquiv p i = leafPermutationTable p i := rfl

theorem subsetForms_leafPermutation : ∀ (p : Fin 24) (q : Fin 15) (i : Fin 4),
    subsetForms q i = subsetForms (leafMaskPermutation p q) (leafPermutationTable p i) := by decide

def reorderLeafPoint (p : Fin 24) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => z (leafPermutationTable p i)

theorem evalForm_reorderLeafPoint (p : Fin 24) (q : Fin 15) (z : Fin 4 → ℝ) :
    evalForm (subsetForms q) (reorderLeafPoint p z) =
      evalForm (subsetForms (leafMaskPermutation p q)) z := by
  unfold evalForm reorderLeafPoint
  apply Fintype.sum_equiv (leafPermutationEquiv p)
  intro i
  rw [leafPermutationEquiv_apply, ← subsetForms_leafPermutation p q i]

theorem actualSigns_reorderLeafPoint (p : Fin 24) (z : Fin 4 → ℝ) :
    actualSigns subsetForms (reorderLeafPoint p z) =
      fun q => actualSigns subsetForms z (leafMaskPermutation p q) := by
  funext q
  exact congrArg signOf (evalForm_reorderLeafPoint p q z)

structure OrbitDescriptor where
  representative : Fin 67
  permutation : Fin 24
  negative : Bool
  deriving DecidableEq, Repr

def orbitRepresentativeLeaf : Fin 67 → Fin 900 := ![0, 1, 2, 3, 4, 6, 7, 10, 11, 12, 17, 18, 21, 22, 23, 36, 37, 38, 40, 41, 44, 51, 52, 55, 66, 67, 68, 70, 71, 72, 73, 75, 76, 79, 80, 81, 86, 87, 88, 90, 91, 94, 95, 96, 97, 98, 99, 100, 104, 105, 110, 111, 112, 113, 114, 122, 123, 124, 125, 126, 127, 128, 175, 313, 314, 315, 850]
def orbitRepresentativePattern (j : Fin 67) : Fin 15 → Sign :=
  if j.val < 33 then (
    if j.val < 16 then (
      if j.val < 8 then (
        if j.val < 4 then (
          if j.val < 2 then (
            if j.val < 1 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
            )
          ) else (
            if j.val < 3 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
            )
          )
        ) else (
          if j.val < 6 then (
            if j.val < 5 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .zero, .neg, .neg, .neg]
            )
          ) else (
            if j.val < 7 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg]
            )
          )
        )
      ) else (
        if j.val < 12 then (
          if j.val < 10 then (
            if j.val < 9 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
            )
          ) else (
            if j.val < 11 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .zero, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .neg, .neg, .neg]
            )
          )
        ) else (
          if j.val < 14 then (
            if j.val < 13 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .zero, .neg]
            )
          ) else (
            if j.val < 15 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .neg, .neg]
            )
          )
        )
      )
    ) else (
      if j.val < 24 then (
        if j.val < 20 then (
          if j.val < 18 then (
            if j.val < 17 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .zero, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .neg]
            )
          ) else (
            if j.val < 19 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .zero, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .neg]
            )
          )
        ) else (
          if j.val < 22 then (
            if j.val < 21 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .zero, .neg]
            )
          ) else (
            if j.val < 23 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .neg]
            )
          )
        )
      ) else (
        if j.val < 28 then (
          if j.val < 26 then (
            if j.val < 25 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .zero]
            )
          ) else (
            if j.val < 27 then (
              ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
            ) else (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
            )
          )
        ) else (
          if j.val < 30 then (
            if j.val < 29 then (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
            ) else (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg]
            )
          ) else (
            if j.val < 31 then (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
            ) else (
              if j.val < 32 then (
                ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .zero, .zero, .neg]
              ) else (
                ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .zero, .pos, .neg]
              )
            )
          )
        )
      )
    )
  ) else (
    if j.val < 50 then (
      if j.val < 41 then (
        if j.val < 37 then (
          if j.val < 35 then (
            if j.val < 34 then (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .zero]
            )
          ) else (
            if j.val < 36 then (
              ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
            )
          )
        ) else (
          if j.val < 39 then (
            if j.val < 38 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
            )
          ) else (
            if j.val < 40 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .zero, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
            )
          )
        )
      ) else (
        if j.val < 45 then (
          if j.val < 43 then (
            if j.val < 42 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
            )
          ) else (
            if j.val < 44 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .neg]
            )
          )
        ) else (
          if j.val < 47 then (
            if j.val < 46 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg]
            )
          ) else (
            if j.val < 48 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg]
            ) else (
              if j.val < 49 then (
                ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .neg]
              ) else (
                ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg]
              )
            )
          )
        )
      )
    ) else (
      if j.val < 58 then (
        if j.val < 54 then (
          if j.val < 52 then (
            if j.val < 51 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero]
            )
          ) else (
            if j.val < 53 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
            )
          )
        ) else (
          if j.val < 56 then (
            if j.val < 55 then (
              ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
            )
          ) else (
            if j.val < 57 then (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .neg]
            )
          )
        )
      ) else (
        if j.val < 62 then (
          if j.val < 60 then (
            if j.val < 59 then (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg]
            )
          ) else (
            if j.val < 61 then (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg]
            ) else (
              ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .zero]
            )
          )
        ) else (
          if j.val < 64 then (
            if j.val < 63 then (
              ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .zero]
            ) else (
              ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg]
            )
          ) else (
            if j.val < 65 then (
              ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
            ) else (
              if j.val < 66 then (
                ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .zero, .pos, .zero]
              ) else (
                ![.zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero]
              )
            )
          )
        )
      )
    )
  )
def orbitLeafPattern (j : Fin 900) : Fin 15 → Sign :=
  if j.val < 450 then (
    if j.val < 225 then (
      if j.val < 112 then (
        if j.val < 56 then (
          if j.val < 28 then (
            if j.val < 14 then (
              if j.val < 7 then (
                if j.val < 3 then (
                  if j.val < 1 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 2 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 5 then (
                    if j.val < 4 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 6 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 10 then (
                  if j.val < 8 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg]
                  ) else (
                    if j.val < 9 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 12 then (
                    if j.val < 11 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 13 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 21 then (
                if j.val < 17 then (
                  if j.val < 15 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg]
                  ) else (
                    if j.val < 16 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 19 then (
                    if j.val < 18 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .zero, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 20 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 24 then (
                  if j.val < 22 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .neg, .neg]
                  ) else (
                    if j.val < 23 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 26 then (
                    if j.val < 25 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 27 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 42 then (
              if j.val < 35 then (
                if j.val < 31 then (
                  if j.val < 29 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                  ) else (
                    if j.val < 30 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 33 then (
                    if j.val < 32 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .zero, .neg, .neg]
                    )
                  ) else (
                    if j.val < 34 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 38 then (
                  if j.val < 36 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .zero, .neg, .neg, .neg]
                  ) else (
                    if j.val < 37 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 40 then (
                    if j.val < 39 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .neg, .neg]
                    )
                  ) else (
                    if j.val < 41 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 49 then (
                if j.val < 45 then (
                  if j.val < 43 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg]
                  ) else (
                    if j.val < 44 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 47 then (
                    if j.val < 46 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .zero, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 48 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .neg, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 52 then (
                  if j.val < 50 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 51 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 54 then (
                    if j.val < 53 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg]
                    )
                  ) else (
                    if j.val < 55 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .neg]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 84 then (
            if j.val < 70 then (
              if j.val < 63 then (
                if j.val < 59 then (
                  if j.val < 57 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 58 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 61 then (
                    if j.val < 60 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 62 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 66 then (
                  if j.val < 64 then (
                    ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .neg]
                  ) else (
                    if j.val < 65 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 68 then (
                    if j.val < 67 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .zero]
                    )
                  ) else (
                    if j.val < 69 then (
                      ![.neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 77 then (
                if j.val < 73 then (
                  if j.val < 71 then (
                    ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                  ) else (
                    if j.val < 72 then (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 75 then (
                    if j.val < 74 then (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg]
                    )
                  ) else (
                    if j.val < 76 then (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .zero, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .zero, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 80 then (
                  if j.val < 78 then (
                    ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                  ) else (
                    if j.val < 79 then (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 82 then (
                    if j.val < 81 then (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .zero]
                    ) else (
                      ![.neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 83 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 98 then (
              if j.val < 91 then (
                if j.val < 87 then (
                  if j.val < 85 then (
                    ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                  ) else (
                    if j.val < 86 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 89 then (
                    if j.val < 88 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 90 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 94 then (
                  if j.val < 92 then (
                    ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                  ) else (
                    if j.val < 93 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 96 then (
                    if j.val < 95 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 97 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 105 then (
                if j.val < 101 then (
                  if j.val < 99 then (
                    ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 100 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 103 then (
                    if j.val < 102 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  ) else (
                    if j.val < 104 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 108 then (
                  if j.val < 106 then (
                    ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg]
                  ) else (
                    if j.val < 107 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 110 then (
                    if j.val < 109 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .neg]
                    )
                  ) else (
                    if j.val < 111 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero]
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 168 then (
          if j.val < 140 then (
            if j.val < 126 then (
              if j.val < 119 then (
                if j.val < 115 then (
                  if j.val < 113 then (
                    ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 114 then (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 117 then (
                    if j.val < 116 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 118 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 122 then (
                  if j.val < 120 then (
                    ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 121 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 124 then (
                    if j.val < 123 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
                    )
                  ) else (
                    if j.val < 125 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 133 then (
                if j.val < 129 then (
                  if j.val < 127 then (
                    ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg]
                  ) else (
                    if j.val < 128 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 131 then (
                    if j.val < 130 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 132 then (
                      ![.neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 136 then (
                  if j.val < 134 then (
                    ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                  ) else (
                    if j.val < 135 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 138 then (
                    if j.val < 137 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 139 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 154 then (
              if j.val < 147 then (
                if j.val < 143 then (
                  if j.val < 141 then (
                    ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                  ) else (
                    if j.val < 142 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 145 then (
                    if j.val < 144 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 146 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 150 then (
                  if j.val < 148 then (
                    ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .zero]
                  ) else (
                    if j.val < 149 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 152 then (
                    if j.val < 151 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 153 then (
                      ![.neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 161 then (
                if j.val < 157 then (
                  if j.val < 155 then (
                    ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                  ) else (
                    if j.val < 156 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 159 then (
                    if j.val < 158 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  ) else (
                    if j.val < 160 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 164 then (
                  if j.val < 162 then (
                    ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .zero, .neg]
                  ) else (
                    if j.val < 163 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 166 then (
                    if j.val < 165 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg]
                    )
                  ) else (
                    if j.val < 167 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .zero]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 196 then (
            if j.val < 182 then (
              if j.val < 175 then (
                if j.val < 171 then (
                  if j.val < 169 then (
                    ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 170 then (
                      ![.neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 173 then (
                    if j.val < 172 then (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 174 then (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 178 then (
                  if j.val < 176 then (
                    ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .zero]
                  ) else (
                    if j.val < 177 then (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 180 then (
                    if j.val < 179 then (
                      ![.neg, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 181 then (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 189 then (
                if j.val < 185 then (
                  if j.val < 183 then (
                    ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                  ) else (
                    if j.val < 184 then (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 187 then (
                    if j.val < 186 then (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .zero]
                    )
                  ) else (
                    if j.val < 188 then (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 192 then (
                  if j.val < 190 then (
                    ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 191 then (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 194 then (
                    if j.val < 193 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 195 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 210 then (
              if j.val < 203 then (
                if j.val < 199 then (
                  if j.val < 197 then (
                    ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                  ) else (
                    if j.val < 198 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 201 then (
                    if j.val < 200 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    )
                  ) else (
                    if j.val < 202 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 206 then (
                  if j.val < 204 then (
                    ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .neg]
                  ) else (
                    if j.val < 205 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 208 then (
                    if j.val < 207 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .zero]
                    )
                  ) else (
                    if j.val < 209 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 217 then (
                if j.val < 213 then (
                  if j.val < 211 then (
                    ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 212 then (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 215 then (
                    if j.val < 214 then (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 216 then (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 221 then (
                  if j.val < 219 then (
                    if j.val < 218 then (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  ) else (
                    if j.val < 220 then (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 223 then (
                    if j.val < 222 then (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 224 then (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            )
          )
        )
      )
    ) else (
      if j.val < 337 then (
        if j.val < 281 then (
          if j.val < 253 then (
            if j.val < 239 then (
              if j.val < 232 then (
                if j.val < 228 then (
                  if j.val < 226 then (
                    ![.neg, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 227 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 230 then (
                    if j.val < 229 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 231 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 235 then (
                  if j.val < 233 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg]
                  ) else (
                    if j.val < 234 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 237 then (
                    if j.val < 236 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    )
                  ) else (
                    if j.val < 238 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 246 then (
                if j.val < 242 then (
                  if j.val < 240 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .zero]
                  ) else (
                    if j.val < 241 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 244 then (
                    if j.val < 243 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 245 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 249 then (
                  if j.val < 247 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 248 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 251 then (
                    if j.val < 250 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 252 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 267 then (
              if j.val < 260 then (
                if j.val < 256 then (
                  if j.val < 254 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                  ) else (
                    if j.val < 255 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 258 then (
                    if j.val < 257 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg]
                    )
                  ) else (
                    if j.val < 259 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 263 then (
                  if j.val < 261 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                  ) else (
                    if j.val < 262 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 265 then (
                    if j.val < 264 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 266 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 274 then (
                if j.val < 270 then (
                  if j.val < 268 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 269 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 272 then (
                    if j.val < 271 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 273 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 277 then (
                  if j.val < 275 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 276 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 279 then (
                    if j.val < 278 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 280 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .zero, .neg]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 309 then (
            if j.val < 295 then (
              if j.val < 288 then (
                if j.val < 284 then (
                  if j.val < 282 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .neg]
                  ) else (
                    if j.val < 283 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 286 then (
                    if j.val < 285 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .neg]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .zero]
                    )
                  ) else (
                    if j.val < 287 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 291 then (
                  if j.val < 289 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 290 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 293 then (
                    if j.val < 292 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 294 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 302 then (
                if j.val < 298 then (
                  if j.val < 296 then (
                    ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 297 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 300 then (
                    if j.val < 299 then (
                      ![.neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 301 then (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 305 then (
                  if j.val < 303 then (
                    ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .zero, .neg]
                  ) else (
                    if j.val < 304 then (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .zero, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 307 then (
                    if j.val < 306 then (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .zero, .zero, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .zero, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 308 then (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .zero, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 323 then (
              if j.val < 316 then (
                if j.val < 312 then (
                  if j.val < 310 then (
                    ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 311 then (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .zero]
                    ) else (
                      ![.neg, .zero, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 314 then (
                    if j.val < 313 then (
                      ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 315 then (
                      ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .zero, .pos, .zero]
                    )
                  )
                )
              ) else (
                if j.val < 319 then (
                  if j.val < 317 then (
                    ![.neg, .zero, .neg, .zero, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 318 then (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 321 then (
                    if j.val < 320 then (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 322 then (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .zero]
                    )
                  )
                )
              )
            ) else (
              if j.val < 330 then (
                if j.val < 326 then (
                  if j.val < 324 then (
                    ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 325 then (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 328 then (
                    if j.val < 327 then (
                      ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .neg, .neg, .neg, .neg, .zero, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 329 then (
                      ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .zero, .neg, .zero, .neg, .pos, .zero, .pos, .zero]
                    )
                  )
                )
              ) else (
                if j.val < 333 then (
                  if j.val < 331 then (
                    ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 332 then (
                      ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 335 then (
                    if j.val < 334 then (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 336 then (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .zero]
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 393 then (
          if j.val < 365 then (
            if j.val < 351 then (
              if j.val < 344 then (
                if j.val < 340 then (
                  if j.val < 338 then (
                    ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 339 then (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 342 then (
                    if j.val < 341 then (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 343 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 347 then (
                  if j.val < 345 then (
                    ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 346 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 349 then (
                    if j.val < 348 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 350 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 358 then (
                if j.val < 354 then (
                  if j.val < 352 then (
                    ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 353 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 356 then (
                    if j.val < 355 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .zero, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 357 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 361 then (
                  if j.val < 359 then (
                    ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 360 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 363 then (
                    if j.val < 362 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 364 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 379 then (
              if j.val < 372 then (
                if j.val < 368 then (
                  if j.val < 366 then (
                    ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 367 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 370 then (
                    if j.val < 369 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 371 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .zero]
                    )
                  )
                )
              ) else (
                if j.val < 375 then (
                  if j.val < 373 then (
                    ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 374 then (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 377 then (
                    if j.val < 376 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 378 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 386 then (
                if j.val < 382 then (
                  if j.val < 380 then (
                    ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 381 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 384 then (
                    if j.val < 383 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .zero, .zero, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 385 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 389 then (
                  if j.val < 387 then (
                    ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .neg]
                  ) else (
                    if j.val < 388 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 391 then (
                    if j.val < 390 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 392 then (
                      ![.neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 421 then (
            if j.val < 407 then (
              if j.val < 400 then (
                if j.val < 396 then (
                  if j.val < 394 then (
                    ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 395 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 398 then (
                    if j.val < 397 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 399 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 403 then (
                  if j.val < 401 then (
                    ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 402 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .zero, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 405 then (
                    if j.val < 404 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 406 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 414 then (
                if j.val < 410 then (
                  if j.val < 408 then (
                    ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .zero]
                  ) else (
                    if j.val < 409 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 412 then (
                    if j.val < 411 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 413 then (
                      ![.neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 417 then (
                  if j.val < 415 then (
                    ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 416 then (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 419 then (
                    if j.val < 418 then (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .zero]
                    )
                  ) else (
                    if j.val < 420 then (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 435 then (
              if j.val < 428 then (
                if j.val < 424 then (
                  if j.val < 422 then (
                    ![.neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 423 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 426 then (
                    if j.val < 425 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 427 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 431 then (
                  if j.val < 429 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .neg]
                  ) else (
                    if j.val < 430 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 433 then (
                    if j.val < 432 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 434 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 442 then (
                if j.val < 438 then (
                  if j.val < 436 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero]
                  ) else (
                    if j.val < 437 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 440 then (
                    if j.val < 439 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 441 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 446 then (
                  if j.val < 444 then (
                    if j.val < 443 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 445 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 448 then (
                    if j.val < 447 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 449 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) else (
    if j.val < 675 then (
      if j.val < 562 then (
        if j.val < 506 then (
          if j.val < 478 then (
            if j.val < 464 then (
              if j.val < 457 then (
                if j.val < 453 then (
                  if j.val < 451 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .neg]
                  ) else (
                    if j.val < 452 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 455 then (
                    if j.val < 454 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 456 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 460 then (
                  if j.val < 458 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 459 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 462 then (
                    if j.val < 461 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 463 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .zero, .pos, .zero, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 471 then (
                if j.val < 467 then (
                  if j.val < 465 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 466 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 469 then (
                    if j.val < 468 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 470 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 474 then (
                  if j.val < 472 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 473 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 476 then (
                    if j.val < 475 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 477 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 492 then (
              if j.val < 485 then (
                if j.val < 481 then (
                  if j.val < 479 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 480 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 483 then (
                    if j.val < 482 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 484 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 488 then (
                  if j.val < 486 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                  ) else (
                    if j.val < 487 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 490 then (
                    if j.val < 489 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 491 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 499 then (
                if j.val < 495 then (
                  if j.val < 493 then (
                    ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 494 then (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 497 then (
                    if j.val < 496 then (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 498 then (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 502 then (
                  if j.val < 500 then (
                    ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                  ) else (
                    if j.val < 501 then (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 504 then (
                    if j.val < 503 then (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 505 then (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 534 then (
            if j.val < 520 then (
              if j.val < 513 then (
                if j.val < 509 then (
                  if j.val < 507 then (
                    ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 508 then (
                      ![.neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 511 then (
                    if j.val < 510 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 512 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 516 then (
                  if j.val < 514 then (
                    ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .zero]
                  ) else (
                    if j.val < 515 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 518 then (
                    if j.val < 517 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 519 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 527 then (
                if j.val < 523 then (
                  if j.val < 521 then (
                    ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 522 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 525 then (
                    if j.val < 524 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 526 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 530 then (
                  if j.val < 528 then (
                    ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 529 then (
                      ![.neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 532 then (
                    if j.val < 531 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 533 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 548 then (
              if j.val < 541 then (
                if j.val < 537 then (
                  if j.val < 535 then (
                    ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 536 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 539 then (
                    if j.val < 538 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 540 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 544 then (
                  if j.val < 542 then (
                    ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 543 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 546 then (
                    if j.val < 545 then (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 547 then (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 555 then (
                if j.val < 551 then (
                  if j.val < 549 then (
                    ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 550 then (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .zero, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 553 then (
                    if j.val < 552 then (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 554 then (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 558 then (
                  if j.val < 556 then (
                    ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 557 then (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 560 then (
                    if j.val < 559 then (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 561 then (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 618 then (
          if j.val < 590 then (
            if j.val < 576 then (
              if j.val < 569 then (
                if j.val < 565 then (
                  if j.val < 563 then (
                    ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .zero]
                  ) else (
                    if j.val < 564 then (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 567 then (
                    if j.val < 566 then (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 568 then (
                      ![.neg, .pos, .zero, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 572 then (
                  if j.val < 570 then (
                    ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 571 then (
                      ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .zero, .neg, .pos, .zero, .zero, .neg, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 574 then (
                    if j.val < 573 then (
                      ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 575 then (
                      ![.neg, .pos, .zero, .zero, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 583 then (
                if j.val < 579 then (
                  if j.val < 577 then (
                    ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 578 then (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 581 then (
                    if j.val < 580 then (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .zero]
                    )
                  ) else (
                    if j.val < 582 then (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 586 then (
                  if j.val < 584 then (
                    ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 585 then (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 588 then (
                    if j.val < 587 then (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 589 then (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 604 then (
              if j.val < 597 then (
                if j.val < 593 then (
                  if j.val < 591 then (
                    ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 592 then (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 595 then (
                    if j.val < 594 then (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .zero, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 596 then (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 600 then (
                  if j.val < 598 then (
                    ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 599 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 602 then (
                    if j.val < 601 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 603 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 611 then (
                if j.val < 607 then (
                  if j.val < 605 then (
                    ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 606 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 609 then (
                    if j.val < 608 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 610 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 614 then (
                  if j.val < 612 then (
                    ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 613 then (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 616 then (
                    if j.val < 615 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 617 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 646 then (
            if j.val < 632 then (
              if j.val < 625 then (
                if j.val < 621 then (
                  if j.val < 619 then (
                    ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 620 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 623 then (
                    if j.val < 622 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 624 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 628 then (
                  if j.val < 626 then (
                    ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 627 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 630 then (
                    if j.val < 629 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .zero]
                    )
                  ) else (
                    if j.val < 631 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 639 then (
                if j.val < 635 then (
                  if j.val < 633 then (
                    ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 634 then (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 637 then (
                    if j.val < 636 then (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 638 then (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 642 then (
                  if j.val < 640 then (
                    ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 641 then (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 644 then (
                    if j.val < 643 then (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 645 then (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 660 then (
              if j.val < 653 then (
                if j.val < 649 then (
                  if j.val < 647 then (
                    ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                  ) else (
                    if j.val < 648 then (
                      ![.neg, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 651 then (
                    if j.val < 650 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 652 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 656 then (
                  if j.val < 654 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 655 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 658 then (
                    if j.val < 657 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 659 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 667 then (
                if j.val < 663 then (
                  if j.val < 661 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 662 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 665 then (
                    if j.val < 664 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 666 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 671 then (
                  if j.val < 669 then (
                    if j.val < 668 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 670 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 673 then (
                    if j.val < 672 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 674 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          )
        )
      )
    ) else (
      if j.val < 787 then (
        if j.val < 731 then (
          if j.val < 703 then (
            if j.val < 689 then (
              if j.val < 682 then (
                if j.val < 678 then (
                  if j.val < 676 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 677 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 680 then (
                    if j.val < 679 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg, .zero, .neg]
                    )
                  ) else (
                    if j.val < 681 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 685 then (
                  if j.val < 683 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 684 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 687 then (
                    if j.val < 686 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 688 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 696 then (
                if j.val < 692 then (
                  if j.val < 690 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .pos]
                  ) else (
                    if j.val < 691 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 694 then (
                    if j.val < 693 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 695 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 699 then (
                  if j.val < 697 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 698 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 701 then (
                    if j.val < 700 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 702 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .zero, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 717 then (
              if j.val < 710 then (
                if j.val < 706 then (
                  if j.val < 704 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .neg]
                  ) else (
                    if j.val < 705 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .neg]
                    )
                  )
                ) else (
                  if j.val < 708 then (
                    if j.val < 707 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .zero]
                    )
                  ) else (
                    if j.val < 709 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 713 then (
                  if j.val < 711 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                  ) else (
                    if j.val < 712 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 715 then (
                    if j.val < 714 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 716 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 724 then (
                if j.val < 720 then (
                  if j.val < 718 then (
                    ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos]
                  ) else (
                    if j.val < 719 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 722 then (
                    if j.val < 721 then (
                      ![.neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 723 then (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 727 then (
                  if j.val < 725 then (
                    ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .zero]
                  ) else (
                    if j.val < 726 then (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 729 then (
                    if j.val < 728 then (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 730 then (
                      ![.neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 759 then (
            if j.val < 745 then (
              if j.val < 738 then (
                if j.val < 734 then (
                  if j.val < 732 then (
                    ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 733 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .neg]
                    )
                  )
                ) else (
                  if j.val < 736 then (
                    if j.val < 735 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .zero]
                    )
                  ) else (
                    if j.val < 737 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 741 then (
                  if j.val < 739 then (
                    ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 740 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 743 then (
                    if j.val < 742 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 744 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 752 then (
                if j.val < 748 then (
                  if j.val < 746 then (
                    ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 747 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 750 then (
                    if j.val < 749 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 751 then (
                      ![.neg, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 755 then (
                  if j.val < 753 then (
                    ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                  ) else (
                    if j.val < 754 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .zero]
                    )
                  )
                ) else (
                  if j.val < 757 then (
                    if j.val < 756 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 758 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 773 then (
              if j.val < 766 then (
                if j.val < 762 then (
                  if j.val < 760 then (
                    ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos]
                  ) else (
                    if j.val < 761 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 764 then (
                    if j.val < 763 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 765 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 769 then (
                  if j.val < 767 then (
                    ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 768 then (
                      ![.neg, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 771 then (
                    if j.val < 770 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .neg]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .neg]
                    )
                  ) else (
                    if j.val < 772 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .zero]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 780 then (
                if j.val < 776 then (
                  if j.val < 774 then (
                    ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .neg, .pos, .pos]
                  ) else (
                    if j.val < 775 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 778 then (
                    if j.val < 777 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .neg, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 779 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 783 then (
                  if j.val < 781 then (
                    ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .zero, .pos, .pos]
                  ) else (
                    if j.val < 782 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .neg, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 785 then (
                    if j.val < 784 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 786 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 843 then (
          if j.val < 815 then (
            if j.val < 801 then (
              if j.val < 794 then (
                if j.val < 790 then (
                  if j.val < 788 then (
                    ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .zero, .neg, .neg, .pos, .pos]
                  ) else (
                    if j.val < 789 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .zero, .zero, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 792 then (
                    if j.val < 791 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .zero, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 793 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 797 then (
                  if j.val < 795 then (
                    ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .neg, .pos, .pos]
                  ) else (
                    if j.val < 796 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .zero, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 799 then (
                    if j.val < 798 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 800 then (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 808 then (
                if j.val < 804 then (
                  if j.val < 802 then (
                    ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 803 then (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 806 then (
                    if j.val < 805 then (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  ) else (
                    if j.val < 807 then (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .zero, .zero, .zero, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 811 then (
                  if j.val < 809 then (
                    ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .neg, .neg]
                  ) else (
                    if j.val < 810 then (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .zero, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 813 then (
                    if j.val < 812 then (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .zero]
                    )
                  ) else (
                    if j.val < 814 then (
                      ![.zero, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 829 then (
              if j.val < 822 then (
                if j.val < 818 then (
                  if j.val < 816 then (
                    ![.zero, .neg, .neg, .zero, .zero, .neg, .neg, .zero, .zero, .neg, .neg, .zero, .zero, .neg, .neg]
                  ) else (
                    if j.val < 817 then (
                      ![.zero, .neg, .neg, .zero, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .zero, .zero, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .zero, .zero]
                    )
                  )
                ) else (
                  if j.val < 820 then (
                    if j.val < 819 then (
                      ![.zero, .neg, .neg, .zero, .zero, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 821 then (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .zero, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 825 then (
                  if j.val < 823 then (
                    ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .pos, .pos, .neg, .neg]
                  ) else (
                    if j.val < 824 then (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .zero]
                    )
                  )
                ) else (
                  if j.val < 827 then (
                    if j.val < 826 then (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 828 then (
                      ![.zero, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              )
            ) else (
              if j.val < 836 then (
                if j.val < 832 then (
                  if j.val < 830 then (
                    ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .zero, .zero, .neg, .neg]
                  ) else (
                    if j.val < 831 then (
                      ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .zero, .zero, .neg, .neg, .pos, .pos, .zero, .zero]
                    )
                  )
                ) else (
                  if j.val < 834 then (
                    if j.val < 833 then (
                      ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .zero, .zero, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 835 then (
                      ![.zero, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 839 then (
                  if j.val < 837 then (
                    ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .zero, .neg, .neg]
                  ) else (
                    if j.val < 838 then (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .zero, .zero]
                    )
                  )
                ) else (
                  if j.val < 841 then (
                    if j.val < 840 then (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .zero, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 842 then (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .zero, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 871 then (
            if j.val < 857 then (
              if j.val < 850 then (
                if j.val < 846 then (
                  if j.val < 844 then (
                    ![.zero, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                  ) else (
                    if j.val < 845 then (
                      ![.zero, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .zero, .zero, .neg, .neg, .neg, .neg, .zero, .zero, .zero, .zero, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 848 then (
                    if j.val < 847 then (
                      ![.zero, .zero, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .zero, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .zero, .zero, .zero]
                    )
                  ) else (
                    if j.val < 849 then (
                      ![.zero, .zero, .zero, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .zero, .zero, .zero, .zero, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                )
              ) else (
                if j.val < 853 then (
                  if j.val < 851 then (
                    ![.zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero]
                  ) else (
                    if j.val < 852 then (
                      ![.zero, .zero, .zero, .zero, .zero, .zero, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .zero, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 855 then (
                    if j.val < 854 then (
                      ![.zero, .zero, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .zero, .zero, .zero]
                    ) else (
                      ![.zero, .zero, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 856 then (
                      ![.zero, .zero, .zero, .pos, .pos, .pos, .pos, .zero, .zero, .zero, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .zero, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 864 then (
                if j.val < 860 then (
                  if j.val < 858 then (
                    ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                  ) else (
                    if j.val < 859 then (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 862 then (
                    if j.val < 861 then (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .zero, .pos, .pos, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 863 then (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .zero]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 867 then (
                  if j.val < 865 then (
                    ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .zero, .zero, .pos, .pos]
                  ) else (
                    if j.val < 866 then (
                      ![.zero, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 869 then (
                    if j.val < 868 then (
                      ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .zero, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 870 then (
                      ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .zero, .zero, .pos, .pos, .neg, .neg, .zero, .zero]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 885 then (
              if j.val < 878 then (
                if j.val < 874 then (
                  if j.val < 872 then (
                    ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .pos, .pos, .pos, .pos, .zero, .zero, .pos, .pos]
                  ) else (
                    if j.val < 873 then (
                      ![.zero, .pos, .pos, .neg, .neg, .zero, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 876 then (
                    if j.val < 875 then (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .neg, .neg]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 877 then (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .zero, .zero]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 881 then (
                  if j.val < 879 then (
                    ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos, .neg, .neg, .pos, .pos]
                  ) else (
                    if j.val < 880 then (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .zero, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 883 then (
                    if j.val < 882 then (
                      ![.zero, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .zero, .zero, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  ) else (
                    if j.val < 884 then (
                      ![.zero, .pos, .pos, .zero, .zero, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .zero, .zero]
                    ) else (
                      ![.zero, .pos, .pos, .zero, .zero, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                )
              )
            ) else (
              if j.val < 892 then (
                if j.val < 888 then (
                  if j.val < 886 then (
                    ![.zero, .pos, .pos, .zero, .zero, .pos, .pos, .zero, .zero, .pos, .pos, .zero, .zero, .pos, .pos]
                  ) else (
                    if j.val < 887 then (
                      ![.zero, .pos, .pos, .zero, .zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .neg, .neg]
                    )
                  )
                ) else (
                  if j.val < 890 then (
                    if j.val < 889 then (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .zero, .zero]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .neg, .neg, .pos, .pos]
                    )
                  ) else (
                    if j.val < 891 then (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .zero, .zero, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .neg, .neg, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              ) else (
                if j.val < 896 then (
                  if j.val < 894 then (
                    if j.val < 893 then (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .zero, .neg, .neg, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .zero, .zero, .zero, .pos, .pos]
                    )
                  ) else (
                    if j.val < 895 then (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .zero, .zero, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .neg, .neg, .pos, .pos]
                    )
                  )
                ) else (
                  if j.val < 898 then (
                    if j.val < 897 then (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .zero, .zero, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .neg, .neg, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  ) else (
                    if j.val < 899 then (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .zero, .zero, .pos, .pos, .pos, .pos, .pos, .pos]
                    ) else (
                      ![.zero, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos, .pos]
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
def orbitDescriptor (j : Fin 900) : OrbitDescriptor :=
  if j.val < 450 then (
    if j.val < 225 then (
      if j.val < 112 then (
        if j.val < 56 then (
          if j.val < 28 then (
            if j.val < 14 then (
              if j.val < 7 then (
                if j.val < 3 then (
                  if j.val < 1 then (
                    ⟨0,0,false⟩
                  ) else (
                    if j.val < 2 then (
                      ⟨1,0,false⟩
                    ) else (
                      ⟨2,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 5 then (
                    if j.val < 4 then (
                      ⟨3,0,false⟩
                    ) else (
                      ⟨4,0,false⟩
                    )
                  ) else (
                    if j.val < 6 then (
                      ⟨3,2,false⟩
                    ) else (
                      ⟨5,0,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 10 then (
                  if j.val < 8 then (
                    ⟨6,0,false⟩
                  ) else (
                    if j.val < 9 then (
                      ⟨4,2,false⟩
                    ) else (
                      ⟨6,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 12 then (
                    if j.val < 11 then (
                      ⟨7,0,false⟩
                    ) else (
                      ⟨8,0,false⟩
                    )
                  ) else (
                    if j.val < 13 then (
                      ⟨9,0,false⟩
                    ) else (
                      ⟨3,8,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 21 then (
                if j.val < 17 then (
                  if j.val < 15 then (
                    ⟨5,6,false⟩
                  ) else (
                    if j.val < 16 then (
                      ⟨6,6,false⟩
                    ) else (
                      ⟨5,12,false⟩
                    )
                  )
                ) else (
                  if j.val < 19 then (
                    if j.val < 18 then (
                      ⟨10,0,false⟩
                    ) else (
                      ⟨11,0,false⟩
                    )
                  ) else (
                    if j.val < 20 then (
                      ⟨6,12,false⟩
                    ) else (
                      ⟨11,2,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 24 then (
                  if j.val < 22 then (
                    ⟨12,0,false⟩
                  ) else (
                    if j.val < 23 then (
                      ⟨13,0,false⟩
                    ) else (
                      ⟨14,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 26 then (
                    if j.val < 25 then (
                      ⟨4,8,false⟩
                    ) else (
                      ⟨6,8,false⟩
                    )
                  ) else (
                    if j.val < 27 then (
                      ⟨7,6,false⟩
                    ) else (
                      ⟨8,6,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 42 then (
              if j.val < 35 then (
                if j.val < 31 then (
                  if j.val < 29 then (
                    ⟨9,6,false⟩
                  ) else (
                    if j.val < 30 then (
                      ⟨6,14,false⟩
                    ) else (
                      ⟨11,8,false⟩
                    )
                  )
                ) else (
                  if j.val < 33 then (
                    if j.val < 32 then (
                      ⟨12,6,false⟩
                    ) else (
                      ⟨13,6,false⟩
                    )
                  ) else (
                    if j.val < 34 then (
                      ⟨14,6,false⟩
                    ) else (
                      ⟨7,12,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 38 then (
                  if j.val < 36 then (
                    ⟨12,12,false⟩
                  ) else (
                    if j.val < 37 then (
                      ⟨15,0,false⟩
                    ) else (
                      ⟨16,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 40 then (
                    if j.val < 39 then (
                      ⟨17,0,false⟩
                    ) else (
                      ⟨16,6,false⟩
                    )
                  ) else (
                    if j.val < 41 then (
                      ⟨18,0,false⟩
                    ) else (
                      ⟨19,0,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 49 then (
                if j.val < 45 then (
                  if j.val < 43 then (
                    ⟨17,6,false⟩
                  ) else (
                    if j.val < 44 then (
                      ⟨19,6,false⟩
                    ) else (
                      ⟨20,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 47 then (
                    if j.val < 46 then (
                      ⟨8,12,false⟩
                    ) else (
                      ⟨13,12,false⟩
                    )
                  ) else (
                    if j.val < 48 then (
                      ⟨16,12,false⟩
                    ) else (
                      ⟨18,2,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 52 then (
                  if j.val < 50 then (
                    ⟨19,2,false⟩
                  ) else (
                    if j.val < 51 then (
                      ⟨18,8,false⟩
                    ) else (
                      ⟨21,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 54 then (
                    if j.val < 53 then (
                      ⟨22,0,false⟩
                    ) else (
                      ⟨19,8,false⟩
                    )
                  ) else (
                    if j.val < 55 then (
                      ⟨22,6,false⟩
                    ) else (
                      ⟨23,0,false⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 84 then (
            if j.val < 70 then (
              if j.val < 63 then (
                if j.val < 59 then (
                  if j.val < 57 then (
                    ⟨9,12,false⟩
                  ) else (
                    if j.val < 58 then (
                      ⟨14,12,false⟩
                    ) else (
                      ⟨17,12,false⟩
                    )
                  )
                ) else (
                  if j.val < 61 then (
                    if j.val < 60 then (
                      ⟨19,12,false⟩
                    ) else (
                      ⟨20,2,false⟩
                    )
                  ) else (
                    if j.val < 62 then (
                      ⟨19,14,false⟩
                    ) else (
                      ⟨22,12,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 66 then (
                  if j.val < 64 then (
                    ⟨23,2,false⟩
                  ) else (
                    if j.val < 65 then (
                      ⟨20,8,false⟩
                    ) else (
                      ⟨23,8,false⟩
                    )
                  )
                ) else (
                  if j.val < 68 then (
                    if j.val < 67 then (
                      ⟨24,0,false⟩
                    ) else (
                      ⟨25,0,false⟩
                    )
                  ) else (
                    if j.val < 69 then (
                      ⟨26,0,false⟩
                    ) else (
                      ⟨1,1,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 77 then (
                if j.val < 73 then (
                  if j.val < 71 then (
                    ⟨27,0,false⟩
                  ) else (
                    if j.val < 72 then (
                      ⟨28,0,false⟩
                    ) else (
                      ⟨29,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 75 then (
                    if j.val < 74 then (
                      ⟨30,0,false⟩
                    ) else (
                      ⟨29,6,false⟩
                    )
                  ) else (
                    if j.val < 76 then (
                      ⟨31,0,false⟩
                    ) else (
                      ⟨32,0,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 80 then (
                  if j.val < 78 then (
                    ⟨30,6,false⟩
                  ) else (
                    if j.val < 79 then (
                      ⟨32,6,false⟩
                    ) else (
                      ⟨33,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 82 then (
                    if j.val < 81 then (
                      ⟨34,0,false⟩
                    ) else (
                      ⟨35,0,false⟩
                    )
                  ) else (
                    if j.val < 83 then (
                      ⟨2,1,false⟩
                    ) else (
                      ⟨3,1,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 98 then (
              if j.val < 91 then (
                if j.val < 87 then (
                  if j.val < 85 then (
                    ⟨4,1,false⟩
                  ) else (
                    if j.val < 86 then (
                      ⟨28,1,false⟩
                    ) else (
                      ⟨36,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 89 then (
                    if j.val < 88 then (
                      ⟨37,0,false⟩
                    ) else (
                      ⟨38,0,false⟩
                    )
                  ) else (
                    if j.val < 90 then (
                      ⟨37,6,false⟩
                    ) else (
                      ⟨39,0,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 94 then (
                  if j.val < 92 then (
                    ⟨40,0,false⟩
                  ) else (
                    if j.val < 93 then (
                      ⟨38,6,false⟩
                    ) else (
                      ⟨40,6,false⟩
                    )
                  )
                ) else (
                  if j.val < 96 then (
                    if j.val < 95 then (
                      ⟨41,0,false⟩
                    ) else (
                      ⟨42,0,false⟩
                    )
                  ) else (
                    if j.val < 97 then (
                      ⟨43,0,false⟩
                    ) else (
                      ⟨44,0,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 105 then (
                if j.val < 101 then (
                  if j.val < 99 then (
                    ⟨45,0,false⟩
                  ) else (
                    if j.val < 100 then (
                      ⟨46,0,false⟩
                    ) else (
                      ⟨47,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 103 then (
                    if j.val < 102 then (
                      ⟨42,6,false⟩
                    ) else (
                      ⟨43,6,false⟩
                    )
                  ) else (
                    if j.val < 104 then (
                      ⟨44,6,false⟩
                    ) else (
                      ⟨48,0,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 108 then (
                  if j.val < 106 then (
                    ⟨49,0,false⟩
                  ) else (
                    if j.val < 107 then (
                      ⟨45,6,false⟩
                    ) else (
                      ⟨46,6,false⟩
                    )
                  )
                ) else (
                  if j.val < 110 then (
                    if j.val < 109 then (
                      ⟨47,6,false⟩
                    ) else (
                      ⟨49,6,false⟩
                    )
                  ) else (
                    if j.val < 111 then (
                      ⟨50,0,false⟩
                    ) else (
                      ⟨51,0,false⟩
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 168 then (
          if j.val < 140 then (
            if j.val < 126 then (
              if j.val < 119 then (
                if j.val < 115 then (
                  if j.val < 113 then (
                    ⟨52,0,false⟩
                  ) else (
                    if j.val < 114 then (
                      ⟨53,0,false⟩
                    ) else (
                      ⟨54,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 117 then (
                    if j.val < 116 then (
                      ⟨3,4,false⟩
                    ) else (
                      ⟨5,1,false⟩
                    )
                  ) else (
                    if j.val < 118 then (
                      ⟨6,1,false⟩
                    ) else (
                      ⟨29,1,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 122 then (
                  if j.val < 120 then (
                    ⟨42,1,false⟩
                  ) else (
                    if j.val < 121 then (
                      ⟨43,1,false⟩
                    ) else (
                      ⟨44,1,false⟩
                    )
                  )
                ) else (
                  if j.val < 124 then (
                    if j.val < 123 then (
                      ⟨55,0,false⟩
                    ) else (
                      ⟨56,0,false⟩
                    )
                  ) else (
                    if j.val < 125 then (
                      ⟨57,0,false⟩
                    ) else (
                      ⟨58,0,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 133 then (
                if j.val < 129 then (
                  if j.val < 127 then (
                    ⟨59,0,false⟩
                  ) else (
                    if j.val < 128 then (
                      ⟨60,0,false⟩
                    ) else (
                      ⟨61,0,false⟩
                    )
                  )
                ) else (
                  if j.val < 131 then (
                    if j.val < 130 then (
                      ⟨60,23,true⟩
                    ) else (
                      ⟨59,23,true⟩
                    )
                  ) else (
                    if j.val < 132 then (
                      ⟨58,23,true⟩
                    ) else (
                      ⟨4,4,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 136 then (
                  if j.val < 134 then (
                    ⟨6,4,false⟩
                  ) else (
                    if j.val < 135 then (
                      ⟨7,1,false⟩
                    ) else (
                      ⟨8,1,false⟩
                    )
                  )
                ) else (
                  if j.val < 138 then (
                    if j.val < 137 then (
                      ⟨9,1,false⟩
                    ) else (
                      ⟨30,1,false⟩
                    )
                  ) else (
                    if j.val < 139 then (
                      ⟨45,1,false⟩
                    ) else (
                      ⟨46,1,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 154 then (
              if j.val < 147 then (
                if j.val < 143 then (
                  if j.val < 141 then (
                    ⟨47,1,false⟩
                  ) else (
                    if j.val < 142 then (
                      ⟨58,1,false⟩
                    ) else (
                      ⟨59,1,false⟩
                    )
                  )
                ) else (
                  if j.val < 145 then (
                    if j.val < 144 then (
                      ⟨60,1,false⟩
                    ) else (
                      ⟨54,17,true⟩
                    )
                  ) else (
                    if j.val < 146 then (
                      ⟨53,17,true⟩
                    ) else (
                      ⟨52,17,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 150 then (
                  if j.val < 148 then (
                    ⟨51,17,true⟩
                  ) else (
                    if j.val < 149 then (
                      ⟨50,17,true⟩
                    ) else (
                      ⟨49,23,true⟩
                    )
                  )
                ) else (
                  if j.val < 152 then (
                    if j.val < 151 then (
                      ⟨47,23,true⟩
                    ) else (
                      ⟨46,23,true⟩
                    )
                  ) else (
                    if j.val < 153 then (
                      ⟨45,23,true⟩
                    ) else (
                      ⟨3,10,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 161 then (
                if j.val < 157 then (
                  if j.val < 155 then (
                    ⟨5,7,false⟩
                  ) else (
                    if j.val < 156 then (
                      ⟨6,7,false⟩
                    ) else (
                      ⟨29,7,false⟩
                    )
                  )
                ) else (
                  if j.val < 159 then (
                    if j.val < 158 then (
                      ⟨42,7,false⟩
                    ) else (
                      ⟨43,7,false⟩
                    )
                  ) else (
                    if j.val < 160 then (
                      ⟨44,7,false⟩
                    ) else (
                      ⟨55,6,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 164 then (
                  if j.val < 162 then (
                    ⟨56,6,false⟩
                  ) else (
                    if j.val < 163 then (
                      ⟨57,6,false⟩
                    ) else (
                      ⟨58,6,false⟩
                    )
                  )
                ) else (
                  if j.val < 166 then (
                    if j.val < 165 then (
                      ⟨59,6,false⟩
                    ) else (
                      ⟨60,6,false⟩
                    )
                  ) else (
                    if j.val < 167 then (
                      ⟨61,6,false⟩
                    ) else (
                      ⟨60,22,true⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 196 then (
            if j.val < 182 then (
              if j.val < 175 then (
                if j.val < 171 then (
                  if j.val < 169 then (
                    ⟨59,22,true⟩
                  ) else (
                    if j.val < 170 then (
                      ⟨58,22,true⟩
                    ) else (
                      ⟨5,18,false⟩
                    )
                  )
                ) else (
                  if j.val < 173 then (
                    if j.val < 172 then (
                      ⟨10,1,false⟩
                    ) else (
                      ⟨11,1,false⟩
                    )
                  ) else (
                    if j.val < 174 then (
                      ⟨31,1,false⟩
                    ) else (
                      ⟨48,1,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 178 then (
                  if j.val < 176 then (
                    ⟨62,0,false⟩
                  ) else (
                    if j.val < 177 then (
                      ⟨57,22,true⟩
                    ) else (
                      ⟨56,22,true⟩
                    )
                  )
                ) else (
                  if j.val < 180 then (
                    if j.val < 179 then (
                      ⟨55,22,true⟩
                    ) else (
                      ⟨6,18,false⟩
                    )
                  ) else (
                    if j.val < 181 then (
                      ⟨11,4,false⟩
                    ) else (
                      ⟨12,1,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 189 then (
                if j.val < 185 then (
                  if j.val < 183 then (
                    ⟨13,1,false⟩
                  ) else (
                    if j.val < 184 then (
                      ⟨14,1,false⟩
                    ) else (
                      ⟨32,1,false⟩
                    )
                  )
                ) else (
                  if j.val < 187 then (
                    if j.val < 186 then (
                      ⟨49,1,false⟩
                    ) else (
                      ⟨61,1,false⟩
                    )
                  ) else (
                    if j.val < 188 then (
                      ⟨49,17,true⟩
                    ) else (
                      ⟨48,17,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 192 then (
                  if j.val < 190 then (
                    ⟨44,23,true⟩
                  ) else (
                    if j.val < 191 then (
                      ⟨43,23,true⟩
                    ) else (
                      ⟨42,23,true⟩
                    )
                  )
                ) else (
                  if j.val < 194 then (
                    if j.val < 193 then (
                      ⟨4,10,false⟩
                    ) else (
                      ⟨6,10,false⟩
                    )
                  ) else (
                    if j.val < 195 then (
                      ⟨7,7,false⟩
                    ) else (
                      ⟨8,7,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 210 then (
              if j.val < 203 then (
                if j.val < 199 then (
                  if j.val < 197 then (
                    ⟨9,7,false⟩
                  ) else (
                    if j.val < 198 then (
                      ⟨30,7,false⟩
                    ) else (
                      ⟨45,7,false⟩
                    )
                  )
                ) else (
                  if j.val < 201 then (
                    if j.val < 200 then (
                      ⟨46,7,false⟩
                    ) else (
                      ⟨47,7,false⟩
                    )
                  ) else (
                    if j.val < 202 then (
                      ⟨58,7,false⟩
                    ) else (
                      ⟨59,7,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 206 then (
                  if j.val < 204 then (
                    ⟨60,7,false⟩
                  ) else (
                    if j.val < 205 then (
                      ⟨54,16,true⟩
                    ) else (
                      ⟨53,16,true⟩
                    )
                  )
                ) else (
                  if j.val < 208 then (
                    if j.val < 207 then (
                      ⟨52,16,true⟩
                    ) else (
                      ⟨51,16,true⟩
                    )
                  ) else (
                    if j.val < 209 then (
                      ⟨50,16,true⟩
                    ) else (
                      ⟨49,22,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 217 then (
                if j.val < 213 then (
                  if j.val < 211 then (
                    ⟨47,22,true⟩
                  ) else (
                    if j.val < 212 then (
                      ⟨46,22,true⟩
                    ) else (
                      ⟨45,22,true⟩
                    )
                  )
                ) else (
                  if j.val < 215 then (
                    if j.val < 214 then (
                      ⟨6,20,false⟩
                    ) else (
                      ⟨11,10,false⟩
                    )
                  ) else (
                    if j.val < 216 then (
                      ⟨12,7,false⟩
                    ) else (
                      ⟨13,7,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 221 then (
                  if j.val < 219 then (
                    if j.val < 218 then (
                      ⟨14,7,false⟩
                    ) else (
                      ⟨32,7,false⟩
                    )
                  ) else (
                    if j.val < 220 then (
                      ⟨49,7,false⟩
                    ) else (
                      ⟨61,7,false⟩
                    )
                  )
                ) else (
                  if j.val < 223 then (
                    if j.val < 222 then (
                      ⟨49,16,true⟩
                    ) else (
                      ⟨48,16,true⟩
                    )
                  ) else (
                    if j.val < 224 then (
                      ⟨44,22,true⟩
                    ) else (
                      ⟨43,22,true⟩
                    )
                  )
                )
              )
            )
          )
        )
      )
    ) else (
      if j.val < 337 then (
        if j.val < 281 then (
          if j.val < 253 then (
            if j.val < 239 then (
              if j.val < 232 then (
                if j.val < 228 then (
                  if j.val < 226 then (
                    ⟨42,22,true⟩
                  ) else (
                    if j.val < 227 then (
                      ⟨7,18,false⟩
                    ) else (
                      ⟨12,18,false⟩
                    )
                  )
                ) else (
                  if j.val < 230 then (
                    if j.val < 229 then (
                      ⟨15,1,false⟩
                    ) else (
                      ⟨16,1,false⟩
                    )
                  ) else (
                    if j.val < 231 then (
                      ⟨17,1,false⟩
                    ) else (
                      ⟨16,7,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 235 then (
                  if j.val < 233 then (
                    ⟨18,1,false⟩
                  ) else (
                    if j.val < 234 then (
                      ⟨19,1,false⟩
                    ) else (
                      ⟨17,7,false⟩
                    )
                  )
                ) else (
                  if j.val < 237 then (
                    if j.val < 236 then (
                      ⟨19,7,false⟩
                    ) else (
                      ⟨20,1,false⟩
                    )
                  ) else (
                    if j.val < 238 then (
                      ⟨33,1,false⟩
                    ) else (
                      ⟨50,1,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 246 then (
                if j.val < 242 then (
                  if j.val < 240 then (
                    ⟨51,1,false⟩
                  ) else (
                    if j.val < 241 then (
                      ⟨52,1,false⟩
                    ) else (
                      ⟨60,17,true⟩
                    )
                  )
                ) else (
                  if j.val < 244 then (
                    if j.val < 243 then (
                      ⟨47,17,true⟩
                    ) else (
                      ⟨60,16,true⟩
                    )
                  ) else (
                    if j.val < 245 then (
                      ⟨57,16,true⟩
                    ) else (
                      ⟨44,17,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 249 then (
                  if j.val < 247 then (
                    ⟨47,16,true⟩
                  ) else (
                    if j.val < 248 then (
                      ⟨44,16,true⟩
                    ) else (
                      ⟨41,16,true⟩
                    )
                  )
                ) else (
                  if j.val < 251 then (
                    if j.val < 250 then (
                      ⟨40,22,true⟩
                    ) else (
                      ⟨38,22,true⟩
                    )
                  ) else (
                    if j.val < 252 then (
                      ⟨8,18,false⟩
                    ) else (
                      ⟨13,18,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 267 then (
              if j.val < 260 then (
                if j.val < 256 then (
                  if j.val < 254 then (
                    ⟨16,18,false⟩
                  ) else (
                    if j.val < 255 then (
                      ⟨18,4,false⟩
                    ) else (
                      ⟨19,4,false⟩
                    )
                  )
                ) else (
                  if j.val < 258 then (
                    if j.val < 257 then (
                      ⟨18,10,false⟩
                    ) else (
                      ⟨21,1,false⟩
                    )
                  ) else (
                    if j.val < 259 then (
                      ⟨22,1,false⟩
                    ) else (
                      ⟨19,10,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 263 then (
                  if j.val < 261 then (
                    ⟨22,7,false⟩
                  ) else (
                    if j.val < 262 then (
                      ⟨23,1,false⟩
                    ) else (
                      ⟨34,1,false⟩
                    )
                  )
                ) else (
                  if j.val < 265 then (
                    if j.val < 264 then (
                      ⟨53,1,false⟩
                    ) else (
                      ⟨59,17,true⟩
                    )
                  ) else (
                    if j.val < 266 then (
                      ⟨46,17,true⟩
                    ) else (
                      ⟨59,16,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 274 then (
                if j.val < 270 then (
                  if j.val < 268 then (
                    ⟨56,16,true⟩
                  ) else (
                    if j.val < 269 then (
                      ⟨43,17,true⟩
                    ) else (
                      ⟨46,16,true⟩
                    )
                  )
                ) else (
                  if j.val < 272 then (
                    if j.val < 271 then (
                      ⟨43,16,true⟩
                    ) else (
                      ⟨40,16,true⟩
                    )
                  ) else (
                    if j.val < 273 then (
                      ⟨39,16,true⟩
                    ) else (
                      ⟨37,22,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 277 then (
                  if j.val < 275 then (
                    ⟨9,18,false⟩
                  ) else (
                    if j.val < 276 then (
                      ⟨14,18,false⟩
                    ) else (
                      ⟨17,18,false⟩
                    )
                  )
                ) else (
                  if j.val < 279 then (
                    if j.val < 278 then (
                      ⟨19,18,false⟩
                    ) else (
                      ⟨20,4,false⟩
                    )
                  ) else (
                    if j.val < 280 then (
                      ⟨19,20,false⟩
                    ) else (
                      ⟨22,18,false⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 309 then (
            if j.val < 295 then (
              if j.val < 288 then (
                if j.val < 284 then (
                  if j.val < 282 then (
                    ⟨23,4,false⟩
                  ) else (
                    if j.val < 283 then (
                      ⟨20,10,false⟩
                    ) else (
                      ⟨23,10,false⟩
                    )
                  )
                ) else (
                  if j.val < 286 then (
                    if j.val < 285 then (
                      ⟨24,1,false⟩
                    ) else (
                      ⟨25,1,false⟩
                    )
                  ) else (
                    if j.val < 287 then (
                      ⟨26,1,false⟩
                    ) else (
                      ⟨35,1,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 291 then (
                  if j.val < 289 then (
                    ⟨54,1,false⟩
                  ) else (
                    if j.val < 290 then (
                      ⟨58,17,true⟩
                    ) else (
                      ⟨45,17,true⟩
                    )
                  )
                ) else (
                  if j.val < 293 then (
                    if j.val < 292 then (
                      ⟨58,16,true⟩
                    ) else (
                      ⟨55,16,true⟩
                    )
                  ) else (
                    if j.val < 294 then (
                      ⟨42,17,true⟩
                    ) else (
                      ⟨45,16,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 302 then (
                if j.val < 298 then (
                  if j.val < 296 then (
                    ⟨42,16,true⟩
                  ) else (
                    if j.val < 297 then (
                      ⟨38,16,true⟩
                    ) else (
                      ⟨37,16,true⟩
                    )
                  )
                ) else (
                  if j.val < 300 then (
                    if j.val < 299 then (
                      ⟨36,16,true⟩
                    ) else (
                      ⟨1,3,false⟩
                    )
                  ) else (
                    if j.val < 301 then (
                      ⟨27,2,false⟩
                    ) else (
                      ⟨28,2,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 305 then (
                  if j.val < 303 then (
                    ⟨29,2,false⟩
                  ) else (
                    if j.val < 304 then (
                      ⟨30,2,false⟩
                    ) else (
                      ⟨29,12,false⟩
                    )
                  )
                ) else (
                  if j.val < 307 then (
                    if j.val < 306 then (
                      ⟨31,2,false⟩
                    ) else (
                      ⟨32,2,false⟩
                    )
                  ) else (
                    if j.val < 308 then (
                      ⟨30,12,false⟩
                    ) else (
                      ⟨32,12,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 323 then (
              if j.val < 316 then (
                if j.val < 312 then (
                  if j.val < 310 then (
                    ⟨33,2,false⟩
                  ) else (
                    if j.val < 311 then (
                      ⟨34,2,false⟩
                    ) else (
                      ⟨35,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 314 then (
                    if j.val < 313 then (
                      ⟨27,4,false⟩
                    ) else (
                      ⟨63,0,false⟩
                    )
                  ) else (
                    if j.val < 315 then (
                      ⟨64,0,false⟩
                    ) else (
                      ⟨65,0,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 319 then (
                  if j.val < 317 then (
                    ⟨64,21,true⟩
                  ) else (
                    if j.val < 318 then (
                      ⟨28,4,false⟩
                    ) else (
                      ⟨29,4,false⟩
                    )
                  )
                ) else (
                  if j.val < 321 then (
                    if j.val < 320 then (
                      ⟨30,4,false⟩
                    ) else (
                      ⟨64,1,false⟩
                    )
                  ) else (
                    if j.val < 322 then (
                      ⟨35,17,true⟩
                    ) else (
                      ⟨34,17,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 330 then (
                if j.val < 326 then (
                  if j.val < 324 then (
                    ⟨33,17,true⟩
                  ) else (
                    if j.val < 325 then (
                      ⟨32,23,true⟩
                    ) else (
                      ⟨30,23,true⟩
                    )
                  )
                ) else (
                  if j.val < 328 then (
                    if j.val < 327 then (
                      ⟨29,18,false⟩
                    ) else (
                      ⟨31,4,false⟩
                    )
                  ) else (
                    if j.val < 329 then (
                      ⟨32,4,false⟩
                    ) else (
                      ⟨65,1,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 333 then (
                  if j.val < 331 then (
                    ⟨32,17,true⟩
                  ) else (
                    if j.val < 332 then (
                      ⟨31,17,true⟩
                    ) else (
                      ⟨29,23,true⟩
                    )
                  )
                ) else (
                  if j.val < 335 then (
                    if j.val < 334 then (
                      ⟨30,18,false⟩
                    ) else (
                      ⟨32,18,false⟩
                    )
                  ) else (
                    if j.val < 336 then (
                      ⟨33,4,false⟩
                    ) else (
                      ⟨34,4,false⟩
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 393 then (
          if j.val < 365 then (
            if j.val < 351 then (
              if j.val < 344 then (
                if j.val < 340 then (
                  if j.val < 338 then (
                    ⟨35,4,false⟩
                  ) else (
                    if j.val < 339 then (
                      ⟨64,15,true⟩
                    ) else (
                      ⟨30,17,true⟩
                    )
                  )
                ) else (
                  if j.val < 342 then (
                    if j.val < 341 then (
                      ⟨29,17,true⟩
                    ) else (
                      ⟨28,17,true⟩
                    )
                  ) else (
                    if j.val < 343 then (
                      ⟨2,3,false⟩
                    ) else (
                      ⟨3,3,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 347 then (
                  if j.val < 345 then (
                    ⟨4,3,false⟩
                  ) else (
                    if j.val < 346 then (
                      ⟨28,3,false⟩
                    ) else (
                      ⟨36,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 349 then (
                    if j.val < 348 then (
                      ⟨37,2,false⟩
                    ) else (
                      ⟨38,2,false⟩
                    )
                  ) else (
                    if j.val < 350 then (
                      ⟨42,2,false⟩
                    ) else (
                      ⟨45,2,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 358 then (
                if j.val < 354 then (
                  if j.val < 352 then (
                    ⟨37,12,false⟩
                  ) else (
                    if j.val < 353 then (
                      ⟨39,2,false⟩
                    ) else (
                      ⟨40,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 356 then (
                    if j.val < 355 then (
                      ⟨43,2,false⟩
                    ) else (
                      ⟨46,2,false⟩
                    )
                  ) else (
                    if j.val < 357 then (
                      ⟨38,12,false⟩
                    ) else (
                      ⟨40,12,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 361 then (
                  if j.val < 359 then (
                    ⟨41,2,false⟩
                  ) else (
                    if j.val < 360 then (
                      ⟨44,2,false⟩
                    ) else (
                      ⟨47,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 363 then (
                    if j.val < 362 then (
                      ⟨42,12,false⟩
                    ) else (
                      ⟨43,12,false⟩
                    )
                  ) else (
                    if j.val < 364 then (
                      ⟨44,12,false⟩
                    ) else (
                      ⟨48,2,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 379 then (
              if j.val < 372 then (
                if j.val < 368 then (
                  if j.val < 366 then (
                    ⟨49,2,false⟩
                  ) else (
                    if j.val < 367 then (
                      ⟨45,12,false⟩
                    ) else (
                      ⟨46,12,false⟩
                    )
                  )
                ) else (
                  if j.val < 370 then (
                    if j.val < 369 then (
                      ⟨47,12,false⟩
                    ) else (
                      ⟨49,12,false⟩
                    )
                  ) else (
                    if j.val < 371 then (
                      ⟨50,2,false⟩
                    ) else (
                      ⟨51,2,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 375 then (
                  if j.val < 373 then (
                    ⟨52,2,false⟩
                  ) else (
                    if j.val < 374 then (
                      ⟨53,2,false⟩
                    ) else (
                      ⟨54,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 377 then (
                    if j.val < 376 then (
                      ⟨3,5,false⟩
                    ) else (
                      ⟨5,3,false⟩
                    )
                  ) else (
                    if j.val < 378 then (
                      ⟨6,3,false⟩
                    ) else (
                      ⟨29,3,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 386 then (
                if j.val < 382 then (
                  if j.val < 380 then (
                    ⟨42,3,false⟩
                  ) else (
                    if j.val < 381 then (
                      ⟨55,2,false⟩
                    ) else (
                      ⟨58,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 384 then (
                    if j.val < 383 then (
                      ⟨43,3,false⟩
                    ) else (
                      ⟨56,2,false⟩
                    )
                  ) else (
                    if j.val < 385 then (
                      ⟨59,2,false⟩
                    ) else (
                      ⟨44,3,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 389 then (
                  if j.val < 387 then (
                    ⟨57,2,false⟩
                  ) else (
                    if j.val < 388 then (
                      ⟨60,2,false⟩
                    ) else (
                      ⟨61,2,false⟩
                    )
                  )
                ) else (
                  if j.val < 391 then (
                    if j.val < 390 then (
                      ⟨60,21,true⟩
                    ) else (
                      ⟨59,21,true⟩
                    )
                  ) else (
                    if j.val < 392 then (
                      ⟨58,21,true⟩
                    ) else (
                      ⟨4,5,false⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 421 then (
            if j.val < 407 then (
              if j.val < 400 then (
                if j.val < 396 then (
                  if j.val < 394 then (
                    ⟨6,5,false⟩
                  ) else (
                    if j.val < 395 then (
                      ⟨7,3,false⟩
                    ) else (
                      ⟨8,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 398 then (
                    if j.val < 397 then (
                      ⟨9,3,false⟩
                    ) else (
                      ⟨30,3,false⟩
                    )
                  ) else (
                    if j.val < 399 then (
                      ⟨45,3,false⟩
                    ) else (
                      ⟨58,3,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 403 then (
                  if j.val < 401 then (
                    ⟨54,11,true⟩
                  ) else (
                    if j.val < 402 then (
                      ⟨46,3,false⟩
                    ) else (
                      ⟨59,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 405 then (
                    if j.val < 404 then (
                      ⟨53,11,true⟩
                    ) else (
                      ⟨47,3,false⟩
                    )
                  ) else (
                    if j.val < 406 then (
                      ⟨60,3,false⟩
                    ) else (
                      ⟨52,11,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 414 then (
                if j.val < 410 then (
                  if j.val < 408 then (
                    ⟨51,11,true⟩
                  ) else (
                    if j.val < 409 then (
                      ⟨50,11,true⟩
                    ) else (
                      ⟨49,21,true⟩
                    )
                  )
                ) else (
                  if j.val < 412 then (
                    if j.val < 411 then (
                      ⟨47,21,true⟩
                    ) else (
                      ⟨46,21,true⟩
                    )
                  ) else (
                    if j.val < 413 then (
                      ⟨45,21,true⟩
                    ) else (
                      ⟨28,5,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 417 then (
                  if j.val < 415 then (
                    ⟨29,5,false⟩
                  ) else (
                    if j.val < 416 then (
                      ⟨30,5,false⟩
                    ) else (
                      ⟨64,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 419 then (
                    if j.val < 418 then (
                      ⟨35,11,true⟩
                    ) else (
                      ⟨34,11,true⟩
                    )
                  ) else (
                    if j.val < 420 then (
                      ⟨33,11,true⟩
                    ) else (
                      ⟨32,21,true⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 435 then (
              if j.val < 428 then (
                if j.val < 424 then (
                  if j.val < 422 then (
                    ⟨30,21,true⟩
                  ) else (
                    if j.val < 423 then (
                      ⟨36,4,false⟩
                    ) else (
                      ⟨37,4,false⟩
                    )
                  )
                ) else (
                  if j.val < 426 then (
                    if j.val < 425 then (
                      ⟨38,4,false⟩
                    ) else (
                      ⟨42,4,false⟩
                    )
                  ) else (
                    if j.val < 427 then (
                      ⟨45,4,false⟩
                    ) else (
                      ⟨42,5,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 431 then (
                  if j.val < 429 then (
                    ⟨55,4,false⟩
                  ) else (
                    if j.val < 430 then (
                      ⟨58,4,false⟩
                    ) else (
                      ⟨45,5,false⟩
                    )
                  )
                ) else (
                  if j.val < 433 then (
                    if j.val < 432 then (
                      ⟨58,5,false⟩
                    ) else (
                      ⟨54,9,true⟩
                    )
                  ) else (
                    if j.val < 434 then (
                      ⟨35,9,true⟩
                    ) else (
                      ⟨26,9,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 442 then (
                if j.val < 438 then (
                  if j.val < 436 then (
                    ⟨25,9,true⟩
                  ) else (
                    if j.val < 437 then (
                      ⟨24,9,true⟩
                    ) else (
                      ⟨23,17,true⟩
                    )
                  )
                ) else (
                  if j.val < 440 then (
                    if j.val < 439 then (
                      ⟨20,17,true⟩
                    ) else (
                      ⟨23,11,true⟩
                    )
                  ) else (
                    if j.val < 441 then (
                      ⟨22,21,true⟩
                    ) else (
                      ⟨19,23,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 446 then (
                  if j.val < 444 then (
                    if j.val < 443 then (
                      ⟨20,11,true⟩
                    ) else (
                      ⟨19,21,true⟩
                    )
                  ) else (
                    if j.val < 445 then (
                      ⟨17,21,true⟩
                    ) else (
                      ⟨14,21,true⟩
                    )
                  )
                ) else (
                  if j.val < 448 then (
                    if j.val < 447 then (
                      ⟨9,21,true⟩
                    ) else (
                      ⟨37,18,false⟩
                    )
                  ) else (
                    if j.val < 449 then (
                      ⟨39,4,false⟩
                    ) else (
                      ⟨40,4,false⟩
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) else (
    if j.val < 675 then (
      if j.val < 562 then (
        if j.val < 506 then (
          if j.val < 478 then (
            if j.val < 464 then (
              if j.val < 457 then (
                if j.val < 453 then (
                  if j.val < 451 then (
                    ⟨43,4,false⟩
                  ) else (
                    if j.val < 452 then (
                      ⟨46,4,false⟩
                    ) else (
                      ⟨43,5,false⟩
                    )
                  )
                ) else (
                  if j.val < 455 then (
                    if j.val < 454 then (
                      ⟨56,4,false⟩
                    ) else (
                      ⟨59,4,false⟩
                    )
                  ) else (
                    if j.val < 456 then (
                      ⟨46,5,false⟩
                    ) else (
                      ⟨59,5,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 460 then (
                  if j.val < 458 then (
                    ⟨53,9,true⟩
                  ) else (
                    if j.val < 459 then (
                      ⟨34,9,true⟩
                    ) else (
                      ⟨23,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 462 then (
                    if j.val < 461 then (
                      ⟨22,15,true⟩
                    ) else (
                      ⟨19,17,true⟩
                    )
                  ) else (
                    if j.val < 463 then (
                      ⟨22,9,true⟩
                    ) else (
                      ⟨21,9,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 471 then (
                if j.val < 467 then (
                  if j.val < 465 then (
                    ⟨18,17,true⟩
                  ) else (
                    if j.val < 466 then (
                      ⟨19,11,true⟩
                    ) else (
                      ⟨18,11,true⟩
                    )
                  )
                ) else (
                  if j.val < 469 then (
                    if j.val < 468 then (
                      ⟨16,21,true⟩
                    ) else (
                      ⟨13,21,true⟩
                    )
                  ) else (
                    if j.val < 470 then (
                      ⟨8,21,true⟩
                    ) else (
                      ⟨38,18,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 474 then (
                  if j.val < 472 then (
                    ⟨40,18,false⟩
                  ) else (
                    if j.val < 473 then (
                      ⟨41,4,false⟩
                    ) else (
                      ⟨44,4,false⟩
                    )
                  )
                ) else (
                  if j.val < 476 then (
                    if j.val < 475 then (
                      ⟨47,4,false⟩
                    ) else (
                      ⟨44,5,false⟩
                    )
                  ) else (
                    if j.val < 477 then (
                      ⟨57,4,false⟩
                    ) else (
                      ⟨60,4,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 492 then (
              if j.val < 485 then (
                if j.val < 481 then (
                  if j.val < 479 then (
                    ⟨47,5,false⟩
                  ) else (
                    if j.val < 480 then (
                      ⟨60,5,false⟩
                    ) else (
                      ⟨52,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 483 then (
                    if j.val < 482 then (
                      ⟨51,9,true⟩
                    ) else (
                      ⟨50,9,true⟩
                    )
                  ) else (
                    if j.val < 484 then (
                      ⟨33,9,true⟩
                    ) else (
                      ⟨20,9,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 488 then (
                  if j.val < 486 then (
                    ⟨19,15,true⟩
                  ) else (
                    if j.val < 487 then (
                      ⟨17,15,true⟩
                    ) else (
                      ⟨19,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 490 then (
                    if j.val < 489 then (
                      ⟨18,9,true⟩
                    ) else (
                      ⟨16,15,true⟩
                    )
                  ) else (
                    if j.val < 491 then (
                      ⟨17,9,true⟩
                    ) else (
                      ⟨16,9,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 499 then (
                if j.val < 495 then (
                  if j.val < 493 then (
                    ⟨15,9,true⟩
                  ) else (
                    if j.val < 494 then (
                      ⟨12,21,true⟩
                    ) else (
                      ⟨7,21,true⟩
                    )
                  )
                ) else (
                  if j.val < 497 then (
                    if j.val < 496 then (
                      ⟨42,18,false⟩
                    ) else (
                      ⟨43,18,false⟩
                    )
                  ) else (
                    if j.val < 498 then (
                      ⟨44,18,false⟩
                    ) else (
                      ⟨48,4,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 502 then (
                  if j.val < 500 then (
                    ⟨49,4,false⟩
                  ) else (
                    if j.val < 501 then (
                      ⟨61,4,false⟩
                    ) else (
                      ⟨49,15,true⟩
                    )
                  )
                ) else (
                  if j.val < 504 then (
                    if j.val < 503 then (
                      ⟨32,15,true⟩
                    ) else (
                      ⟨14,15,true⟩
                    )
                  ) else (
                    if j.val < 505 then (
                      ⟨13,15,true⟩
                    ) else (
                      ⟨12,15,true⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 534 then (
            if j.val < 520 then (
              if j.val < 513 then (
                if j.val < 509 then (
                  if j.val < 507 then (
                    ⟨11,17,true⟩
                  ) else (
                    if j.val < 508 then (
                      ⟨6,23,true⟩
                    ) else (
                      ⟨45,18,false⟩
                    )
                  )
                ) else (
                  if j.val < 511 then (
                    if j.val < 510 then (
                      ⟨46,18,false⟩
                    ) else (
                      ⟨47,18,false⟩
                    )
                  ) else (
                    if j.val < 512 then (
                      ⟨49,18,false⟩
                    ) else (
                      ⟨50,4,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 516 then (
                  if j.val < 514 then (
                    ⟨51,4,false⟩
                  ) else (
                    if j.val < 515 then (
                      ⟨52,4,false⟩
                    ) else (
                      ⟨53,4,false⟩
                    )
                  )
                ) else (
                  if j.val < 518 then (
                    if j.val < 517 then (
                      ⟨54,4,false⟩
                    ) else (
                      ⟨60,15,true⟩
                    )
                  ) else (
                    if j.val < 519 then (
                      ⟨59,15,true⟩
                    ) else (
                      ⟨58,15,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 527 then (
                if j.val < 523 then (
                  if j.val < 521 then (
                    ⟨47,15,true⟩
                  ) else (
                    if j.val < 522 then (
                      ⟨46,15,true⟩
                    ) else (
                      ⟨45,15,true⟩
                    )
                  )
                ) else (
                  if j.val < 525 then (
                    if j.val < 524 then (
                      ⟨30,15,true⟩
                    ) else (
                      ⟨9,15,true⟩
                    )
                  ) else (
                    if j.val < 526 then (
                      ⟨8,15,true⟩
                    ) else (
                      ⟨7,15,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 530 then (
                  if j.val < 528 then (
                    ⟨6,17,true⟩
                  ) else (
                    if j.val < 529 then (
                      ⟨4,17,true⟩
                    ) else (
                      ⟨3,16,false⟩
                    )
                  )
                ) else (
                  if j.val < 532 then (
                    if j.val < 531 then (
                      ⟨5,13,false⟩
                    ) else (
                      ⟨6,13,false⟩
                    )
                  ) else (
                    if j.val < 533 then (
                      ⟨29,13,false⟩
                    ) else (
                      ⟨42,13,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 548 then (
              if j.val < 541 then (
                if j.val < 537 then (
                  if j.val < 535 then (
                    ⟨43,13,false⟩
                  ) else (
                    if j.val < 536 then (
                      ⟨44,13,false⟩
                    ) else (
                      ⟨55,12,false⟩
                    )
                  )
                ) else (
                  if j.val < 539 then (
                    if j.val < 538 then (
                      ⟨56,12,false⟩
                    ) else (
                      ⟨57,12,false⟩
                    )
                  ) else (
                    if j.val < 540 then (
                      ⟨58,12,false⟩
                    ) else (
                      ⟨59,12,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 544 then (
                  if j.val < 542 then (
                    ⟨60,12,false⟩
                  ) else (
                    if j.val < 543 then (
                      ⟨61,12,false⟩
                    ) else (
                      ⟨60,20,true⟩
                    )
                  )
                ) else (
                  if j.val < 546 then (
                    if j.val < 545 then (
                      ⟨59,20,true⟩
                    ) else (
                      ⟨58,20,true⟩
                    )
                  ) else (
                    if j.val < 547 then (
                      ⟨5,19,false⟩
                    ) else (
                      ⟨10,3,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 555 then (
                if j.val < 551 then (
                  if j.val < 549 then (
                    ⟨11,3,false⟩
                  ) else (
                    if j.val < 550 then (
                      ⟨31,3,false⟩
                    ) else (
                      ⟨48,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 553 then (
                    if j.val < 552 then (
                      ⟨62,2,false⟩
                    ) else (
                      ⟨57,20,true⟩
                    )
                  ) else (
                    if j.val < 554 then (
                      ⟨56,20,true⟩
                    ) else (
                      ⟨55,20,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 558 then (
                  if j.val < 556 then (
                    ⟨6,19,false⟩
                  ) else (
                    if j.val < 557 then (
                      ⟨11,5,false⟩
                    ) else (
                      ⟨12,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 560 then (
                    if j.val < 559 then (
                      ⟨13,3,false⟩
                    ) else (
                      ⟨14,3,false⟩
                    )
                  ) else (
                    if j.val < 561 then (
                      ⟨32,3,false⟩
                    ) else (
                      ⟨49,3,false⟩
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 618 then (
          if j.val < 590 then (
            if j.val < 576 then (
              if j.val < 569 then (
                if j.val < 565 then (
                  if j.val < 563 then (
                    ⟨61,3,false⟩
                  ) else (
                    if j.val < 564 then (
                      ⟨49,11,true⟩
                    ) else (
                      ⟨48,11,true⟩
                    )
                  )
                ) else (
                  if j.val < 567 then (
                    if j.val < 566 then (
                      ⟨44,21,true⟩
                    ) else (
                      ⟨43,21,true⟩
                    )
                  ) else (
                    if j.val < 568 then (
                      ⟨42,21,true⟩
                    ) else (
                      ⟨29,19,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 572 then (
                  if j.val < 570 then (
                    ⟨31,5,false⟩
                  ) else (
                    if j.val < 571 then (
                      ⟨32,5,false⟩
                    ) else (
                      ⟨65,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 574 then (
                    if j.val < 573 then (
                      ⟨32,11,true⟩
                    ) else (
                      ⟨31,11,true⟩
                    )
                  ) else (
                    if j.val < 575 then (
                      ⟨29,21,true⟩
                    ) else (
                      ⟨42,19,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 583 then (
                if j.val < 579 then (
                  if j.val < 577 then (
                    ⟨43,19,false⟩
                  ) else (
                    if j.val < 578 then (
                      ⟨44,19,false⟩
                    ) else (
                      ⟨48,5,false⟩
                    )
                  )
                ) else (
                  if j.val < 581 then (
                    if j.val < 580 then (
                      ⟨49,5,false⟩
                    ) else (
                      ⟨61,5,false⟩
                    )
                  ) else (
                    if j.val < 582 then (
                      ⟨49,9,true⟩
                    ) else (
                      ⟨32,9,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 586 then (
                  if j.val < 584 then (
                    ⟨14,9,true⟩
                  ) else (
                    if j.val < 585 then (
                      ⟨13,9,true⟩
                    ) else (
                      ⟨12,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 588 then (
                    if j.val < 587 then (
                      ⟨11,11,true⟩
                    ) else (
                      ⟨6,21,true⟩
                    )
                  ) else (
                    if j.val < 589 then (
                      ⟨55,18,false⟩
                    ) else (
                      ⟨56,18,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 604 then (
              if j.val < 597 then (
                if j.val < 593 then (
                  if j.val < 591 then (
                    ⟨57,18,false⟩
                  ) else (
                    if j.val < 592 then (
                      ⟨62,4,false⟩
                    ) else (
                      ⟨48,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 595 then (
                    if j.val < 594 then (
                      ⟨31,9,true⟩
                    ) else (
                      ⟨11,9,true⟩
                    )
                  ) else (
                    if j.val < 596 then (
                      ⟨10,9,true⟩
                    ) else (
                      ⟨5,21,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 600 then (
                  if j.val < 598 then (
                    ⟨58,18,false⟩
                  ) else (
                    if j.val < 599 then (
                      ⟨59,18,false⟩
                    ) else (
                      ⟨60,18,false⟩
                    )
                  )
                ) else (
                  if j.val < 602 then (
                    if j.val < 601 then (
                      ⟨61,18,false⟩
                    ) else (
                      ⟨60,14,true⟩
                    )
                  ) else (
                    if j.val < 603 then (
                      ⟨59,14,true⟩
                    ) else (
                      ⟨58,14,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 611 then (
                if j.val < 607 then (
                  if j.val < 605 then (
                    ⟨57,14,true⟩
                  ) else (
                    if j.val < 606 then (
                      ⟨56,14,true⟩
                    ) else (
                      ⟨55,14,true⟩
                    )
                  )
                ) else (
                  if j.val < 609 then (
                    if j.val < 608 then (
                      ⟨44,15,true⟩
                    ) else (
                      ⟨43,15,true⟩
                    )
                  ) else (
                    if j.val < 610 then (
                      ⟨42,15,true⟩
                    ) else (
                      ⟨29,15,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 614 then (
                  if j.val < 612 then (
                    ⟨6,15,true⟩
                  ) else (
                    if j.val < 613 then (
                      ⟨5,15,true⟩
                    ) else (
                      ⟨3,17,true⟩
                    )
                  )
                ) else (
                  if j.val < 616 then (
                    if j.val < 615 then (
                      ⟨4,16,false⟩
                    ) else (
                      ⟨6,16,false⟩
                    )
                  ) else (
                    if j.val < 617 then (
                      ⟨7,13,false⟩
                    ) else (
                      ⟨8,13,false⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 646 then (
            if j.val < 632 then (
              if j.val < 625 then (
                if j.val < 621 then (
                  if j.val < 619 then (
                    ⟨9,13,false⟩
                  ) else (
                    if j.val < 620 then (
                      ⟨30,13,false⟩
                    ) else (
                      ⟨45,13,false⟩
                    )
                  )
                ) else (
                  if j.val < 623 then (
                    if j.val < 622 then (
                      ⟨46,13,false⟩
                    ) else (
                      ⟨47,13,false⟩
                    )
                  ) else (
                    if j.val < 624 then (
                      ⟨58,13,false⟩
                    ) else (
                      ⟨59,13,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 628 then (
                  if j.val < 626 then (
                    ⟨60,13,false⟩
                  ) else (
                    if j.val < 627 then (
                      ⟨54,10,true⟩
                    ) else (
                      ⟨53,10,true⟩
                    )
                  )
                ) else (
                  if j.val < 630 then (
                    if j.val < 629 then (
                      ⟨52,10,true⟩
                    ) else (
                      ⟨51,10,true⟩
                    )
                  ) else (
                    if j.val < 631 then (
                      ⟨50,10,true⟩
                    ) else (
                      ⟨49,20,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 639 then (
                if j.val < 635 then (
                  if j.val < 633 then (
                    ⟨47,20,true⟩
                  ) else (
                    if j.val < 634 then (
                      ⟨46,20,true⟩
                    ) else (
                      ⟨45,20,true⟩
                    )
                  )
                ) else (
                  if j.val < 637 then (
                    if j.val < 636 then (
                      ⟨6,22,false⟩
                    ) else (
                      ⟨11,16,false⟩
                    )
                  ) else (
                    if j.val < 638 then (
                      ⟨12,13,false⟩
                    ) else (
                      ⟨13,13,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 642 then (
                  if j.val < 640 then (
                    ⟨14,13,false⟩
                  ) else (
                    if j.val < 641 then (
                      ⟨32,13,false⟩
                    ) else (
                      ⟨49,13,false⟩
                    )
                  )
                ) else (
                  if j.val < 644 then (
                    if j.val < 643 then (
                      ⟨61,13,false⟩
                    ) else (
                      ⟨49,10,true⟩
                    )
                  ) else (
                    if j.val < 645 then (
                      ⟨48,10,true⟩
                    ) else (
                      ⟨44,20,true⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 660 then (
              if j.val < 653 then (
                if j.val < 649 then (
                  if j.val < 647 then (
                    ⟨43,20,true⟩
                  ) else (
                    if j.val < 648 then (
                      ⟨42,20,true⟩
                    ) else (
                      ⟨7,19,false⟩
                    )
                  )
                ) else (
                  if j.val < 651 then (
                    if j.val < 650 then (
                      ⟨12,19,false⟩
                    ) else (
                      ⟨15,3,false⟩
                    )
                  ) else (
                    if j.val < 652 then (
                      ⟨16,3,false⟩
                    ) else (
                      ⟨17,3,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 656 then (
                  if j.val < 654 then (
                    ⟨16,13,false⟩
                  ) else (
                    if j.val < 655 then (
                      ⟨18,3,false⟩
                    ) else (
                      ⟨19,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 658 then (
                    if j.val < 657 then (
                      ⟨17,13,false⟩
                    ) else (
                      ⟨19,13,false⟩
                    )
                  ) else (
                    if j.val < 659 then (
                      ⟨20,3,false⟩
                    ) else (
                      ⟨33,3,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 667 then (
                if j.val < 663 then (
                  if j.val < 661 then (
                    ⟨50,3,false⟩
                  ) else (
                    if j.val < 662 then (
                      ⟨51,3,false⟩
                    ) else (
                      ⟨52,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 665 then (
                    if j.val < 664 then (
                      ⟨60,11,true⟩
                    ) else (
                      ⟨47,11,true⟩
                    )
                  ) else (
                    if j.val < 666 then (
                      ⟨60,10,true⟩
                    ) else (
                      ⟨57,10,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 671 then (
                  if j.val < 669 then (
                    if j.val < 668 then (
                      ⟨44,11,true⟩
                    ) else (
                      ⟨47,10,true⟩
                    )
                  ) else (
                    if j.val < 670 then (
                      ⟨44,10,true⟩
                    ) else (
                      ⟨41,10,true⟩
                    )
                  )
                ) else (
                  if j.val < 673 then (
                    if j.val < 672 then (
                      ⟨40,20,true⟩
                    ) else (
                      ⟨38,20,true⟩
                    )
                  ) else (
                    if j.val < 674 then (
                      ⟨8,19,false⟩
                    ) else (
                      ⟨13,19,false⟩
                    )
                  )
                )
              )
            )
          )
        )
      )
    ) else (
      if j.val < 787 then (
        if j.val < 731 then (
          if j.val < 703 then (
            if j.val < 689 then (
              if j.val < 682 then (
                if j.val < 678 then (
                  if j.val < 676 then (
                    ⟨16,19,false⟩
                  ) else (
                    if j.val < 677 then (
                      ⟨18,5,false⟩
                    ) else (
                      ⟨19,5,false⟩
                    )
                  )
                ) else (
                  if j.val < 680 then (
                    if j.val < 679 then (
                      ⟨18,16,false⟩
                    ) else (
                      ⟨21,3,false⟩
                    )
                  ) else (
                    if j.val < 681 then (
                      ⟨22,3,false⟩
                    ) else (
                      ⟨19,16,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 685 then (
                  if j.val < 683 then (
                    ⟨22,13,false⟩
                  ) else (
                    if j.val < 684 then (
                      ⟨23,3,false⟩
                    ) else (
                      ⟨34,3,false⟩
                    )
                  )
                ) else (
                  if j.val < 687 then (
                    if j.val < 686 then (
                      ⟨53,3,false⟩
                    ) else (
                      ⟨59,11,true⟩
                    )
                  ) else (
                    if j.val < 688 then (
                      ⟨46,11,true⟩
                    ) else (
                      ⟨59,10,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 696 then (
                if j.val < 692 then (
                  if j.val < 690 then (
                    ⟨56,10,true⟩
                  ) else (
                    if j.val < 691 then (
                      ⟨43,11,true⟩
                    ) else (
                      ⟨46,10,true⟩
                    )
                  )
                ) else (
                  if j.val < 694 then (
                    if j.val < 693 then (
                      ⟨43,10,true⟩
                    ) else (
                      ⟨40,10,true⟩
                    )
                  ) else (
                    if j.val < 695 then (
                      ⟨39,10,true⟩
                    ) else (
                      ⟨37,20,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 699 then (
                  if j.val < 697 then (
                    ⟨9,19,false⟩
                  ) else (
                    if j.val < 698 then (
                      ⟨14,19,false⟩
                    ) else (
                      ⟨17,19,false⟩
                    )
                  )
                ) else (
                  if j.val < 701 then (
                    if j.val < 700 then (
                      ⟨19,19,false⟩
                    ) else (
                      ⟨20,5,false⟩
                    )
                  ) else (
                    if j.val < 702 then (
                      ⟨19,22,false⟩
                    ) else (
                      ⟨22,19,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 717 then (
              if j.val < 710 then (
                if j.val < 706 then (
                  if j.val < 704 then (
                    ⟨23,5,false⟩
                  ) else (
                    if j.val < 705 then (
                      ⟨20,16,false⟩
                    ) else (
                      ⟨23,16,false⟩
                    )
                  )
                ) else (
                  if j.val < 708 then (
                    if j.val < 707 then (
                      ⟨24,3,false⟩
                    ) else (
                      ⟨25,3,false⟩
                    )
                  ) else (
                    if j.val < 709 then (
                      ⟨26,3,false⟩
                    ) else (
                      ⟨35,3,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 713 then (
                  if j.val < 711 then (
                    ⟨54,3,false⟩
                  ) else (
                    if j.val < 712 then (
                      ⟨58,11,true⟩
                    ) else (
                      ⟨45,11,true⟩
                    )
                  )
                ) else (
                  if j.val < 715 then (
                    if j.val < 714 then (
                      ⟨58,10,true⟩
                    ) else (
                      ⟨55,10,true⟩
                    )
                  ) else (
                    if j.val < 716 then (
                      ⟨42,11,true⟩
                    ) else (
                      ⟨45,10,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 724 then (
                if j.val < 720 then (
                  if j.val < 718 then (
                    ⟨42,10,true⟩
                  ) else (
                    if j.val < 719 then (
                      ⟨38,10,true⟩
                    ) else (
                      ⟨37,10,true⟩
                    )
                  )
                ) else (
                  if j.val < 722 then (
                    if j.val < 721 then (
                      ⟨36,10,true⟩
                    ) else (
                      ⟨30,19,false⟩
                    )
                  ) else (
                    if j.val < 723 then (
                      ⟨32,19,false⟩
                    ) else (
                      ⟨33,5,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 727 then (
                  if j.val < 725 then (
                    ⟨34,5,false⟩
                  ) else (
                    if j.val < 726 then (
                      ⟨35,5,false⟩
                    ) else (
                      ⟨64,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 729 then (
                    if j.val < 728 then (
                      ⟨30,11,true⟩
                    ) else (
                      ⟨29,11,true⟩
                    )
                  ) else (
                    if j.val < 730 then (
                      ⟨28,11,true⟩
                    ) else (
                      ⟨45,19,false⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 759 then (
            if j.val < 745 then (
              if j.val < 738 then (
                if j.val < 734 then (
                  if j.val < 732 then (
                    ⟨46,19,false⟩
                  ) else (
                    if j.val < 733 then (
                      ⟨47,19,false⟩
                    ) else (
                      ⟨49,19,false⟩
                    )
                  )
                ) else (
                  if j.val < 736 then (
                    if j.val < 735 then (
                      ⟨50,5,false⟩
                    ) else (
                      ⟨51,5,false⟩
                    )
                  ) else (
                    if j.val < 737 then (
                      ⟨52,5,false⟩
                    ) else (
                      ⟨60,9,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 741 then (
                  if j.val < 739 then (
                    ⟨47,9,true⟩
                  ) else (
                    if j.val < 740 then (
                      ⟨53,5,false⟩
                    ) else (
                      ⟨59,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 743 then (
                    if j.val < 742 then (
                      ⟨46,9,true⟩
                    ) else (
                      ⟨54,5,false⟩
                    )
                  ) else (
                    if j.val < 744 then (
                      ⟨58,9,true⟩
                    ) else (
                      ⟨45,9,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 752 then (
                if j.val < 748 then (
                  if j.val < 746 then (
                    ⟨30,9,true⟩
                  ) else (
                    if j.val < 747 then (
                      ⟨9,9,true⟩
                    ) else (
                      ⟨8,9,true⟩
                    )
                  )
                ) else (
                  if j.val < 750 then (
                    if j.val < 749 then (
                      ⟨7,9,true⟩
                    ) else (
                      ⟨6,11,true⟩
                    )
                  ) else (
                    if j.val < 751 then (
                      ⟨4,11,true⟩
                    ) else (
                      ⟨58,19,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 755 then (
                  if j.val < 753 then (
                    ⟨59,19,false⟩
                  ) else (
                    if j.val < 754 then (
                      ⟨60,19,false⟩
                    ) else (
                      ⟨61,19,false⟩
                    )
                  )
                ) else (
                  if j.val < 757 then (
                    if j.val < 756 then (
                      ⟨60,8,true⟩
                    ) else (
                      ⟨57,8,true⟩
                    )
                  ) else (
                    if j.val < 758 then (
                      ⟨44,9,true⟩
                    ) else (
                      ⟨59,8,true⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 773 then (
              if j.val < 766 then (
                if j.val < 762 then (
                  if j.val < 760 then (
                    ⟨56,8,true⟩
                  ) else (
                    if j.val < 761 then (
                      ⟨43,9,true⟩
                    ) else (
                      ⟨58,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 764 then (
                    if j.val < 763 then (
                      ⟨55,8,true⟩
                    ) else (
                      ⟨42,9,true⟩
                    )
                  ) else (
                    if j.val < 765 then (
                      ⟨29,9,true⟩
                    ) else (
                      ⟨6,9,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 769 then (
                  if j.val < 767 then (
                    ⟨5,9,true⟩
                  ) else (
                    if j.val < 768 then (
                      ⟨3,11,true⟩
                    ) else (
                      ⟨54,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 771 then (
                    if j.val < 770 then (
                      ⟨53,8,true⟩
                    ) else (
                      ⟨52,8,true⟩
                    )
                  ) else (
                    if j.val < 772 then (
                      ⟨51,8,true⟩
                    ) else (
                      ⟨50,8,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 780 then (
                if j.val < 776 then (
                  if j.val < 774 then (
                    ⟨49,14,true⟩
                  ) else (
                    if j.val < 775 then (
                      ⟨47,14,true⟩
                    ) else (
                      ⟨46,14,true⟩
                    )
                  )
                ) else (
                  if j.val < 778 then (
                    if j.val < 777 then (
                      ⟨45,14,true⟩
                    ) else (
                      ⟨49,8,true⟩
                    )
                  ) else (
                    if j.val < 779 then (
                      ⟨48,8,true⟩
                    ) else (
                      ⟨44,14,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 783 then (
                  if j.val < 781 then (
                    ⟨43,14,true⟩
                  ) else (
                    if j.val < 782 then (
                      ⟨42,14,true⟩
                    ) else (
                      ⟨47,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 785 then (
                    if j.val < 784 then (
                      ⟨44,8,true⟩
                    ) else (
                      ⟨41,8,true⟩
                    )
                  ) else (
                    if j.val < 786 then (
                      ⟨40,14,true⟩
                    ) else (
                      ⟨38,14,true⟩
                    )
                  )
                )
              )
            )
          )
        )
      ) else (
        if j.val < 843 then (
          if j.val < 815 then (
            if j.val < 801 then (
              if j.val < 794 then (
                if j.val < 790 then (
                  if j.val < 788 then (
                    ⟨46,8,true⟩
                  ) else (
                    if j.val < 789 then (
                      ⟨43,8,true⟩
                    ) else (
                      ⟨40,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 792 then (
                    if j.val < 791 then (
                      ⟨39,8,true⟩
                    ) else (
                      ⟨37,14,true⟩
                    )
                  ) else (
                    if j.val < 793 then (
                      ⟨45,8,true⟩
                    ) else (
                      ⟨42,8,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 797 then (
                  if j.val < 795 then (
                    ⟨38,8,true⟩
                  ) else (
                    if j.val < 796 then (
                      ⟨37,8,true⟩
                    ) else (
                      ⟨36,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 799 then (
                    if j.val < 798 then (
                      ⟨28,9,true⟩
                    ) else (
                      ⟨4,9,true⟩
                    )
                  ) else (
                    if j.val < 800 then (
                      ⟨3,9,true⟩
                    ) else (
                      ⟨2,9,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 808 then (
                if j.val < 804 then (
                  if j.val < 802 then (
                    ⟨1,9,false⟩
                  ) else (
                    if j.val < 803 then (
                      ⟨27,8,false⟩
                    ) else (
                      ⟨28,8,false⟩
                    )
                  )
                ) else (
                  if j.val < 806 then (
                    if j.val < 805 then (
                      ⟨29,8,false⟩
                    ) else (
                      ⟨30,8,false⟩
                    )
                  ) else (
                    if j.val < 807 then (
                      ⟨29,14,false⟩
                    ) else (
                      ⟨31,8,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 811 then (
                  if j.val < 809 then (
                    ⟨32,8,false⟩
                  ) else (
                    if j.val < 810 then (
                      ⟨30,14,false⟩
                    ) else (
                      ⟨32,14,false⟩
                    )
                  )
                ) else (
                  if j.val < 813 then (
                    if j.val < 812 then (
                      ⟨33,8,false⟩
                    ) else (
                      ⟨34,8,false⟩
                    )
                  ) else (
                    if j.val < 814 then (
                      ⟨35,8,false⟩
                    ) else (
                      ⟨27,10,false⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 829 then (
              if j.val < 822 then (
                if j.val < 818 then (
                  if j.val < 816 then (
                    ⟨63,6,false⟩
                  ) else (
                    if j.val < 817 then (
                      ⟨64,6,false⟩
                    ) else (
                      ⟨65,6,false⟩
                    )
                  )
                ) else (
                  if j.val < 820 then (
                    if j.val < 819 then (
                      ⟨64,19,true⟩
                    ) else (
                      ⟨28,10,false⟩
                    )
                  ) else (
                    if j.val < 821 then (
                      ⟨29,10,false⟩
                    ) else (
                      ⟨30,10,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 825 then (
                  if j.val < 823 then (
                    ⟨64,7,false⟩
                  ) else (
                    if j.val < 824 then (
                      ⟨35,16,true⟩
                    ) else (
                      ⟨34,16,true⟩
                    )
                  )
                ) else (
                  if j.val < 827 then (
                    if j.val < 826 then (
                      ⟨33,16,true⟩
                    ) else (
                      ⟨32,22,true⟩
                    )
                  ) else (
                    if j.val < 828 then (
                      ⟨30,22,true⟩
                    ) else (
                      ⟨29,20,false⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 836 then (
                if j.val < 832 then (
                  if j.val < 830 then (
                    ⟨31,10,false⟩
                  ) else (
                    if j.val < 831 then (
                      ⟨32,10,false⟩
                    ) else (
                      ⟨65,7,false⟩
                    )
                  )
                ) else (
                  if j.val < 834 then (
                    if j.val < 833 then (
                      ⟨32,16,true⟩
                    ) else (
                      ⟨31,16,true⟩
                    )
                  ) else (
                    if j.val < 835 then (
                      ⟨29,22,true⟩
                    ) else (
                      ⟨30,20,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 839 then (
                  if j.val < 837 then (
                    ⟨32,20,false⟩
                  ) else (
                    if j.val < 838 then (
                      ⟨33,10,false⟩
                    ) else (
                      ⟨34,10,false⟩
                    )
                  )
                ) else (
                  if j.val < 841 then (
                    if j.val < 840 then (
                      ⟨35,10,false⟩
                    ) else (
                      ⟨64,13,true⟩
                    )
                  ) else (
                    if j.val < 842 then (
                      ⟨30,16,true⟩
                    ) else (
                      ⟨29,16,true⟩
                    )
                  )
                )
              )
            )
          )
        ) else (
          if j.val < 871 then (
            if j.val < 857 then (
              if j.val < 850 then (
                if j.val < 846 then (
                  if j.val < 844 then (
                    ⟨28,16,true⟩
                  ) else (
                    if j.val < 845 then (
                      ⟨27,16,false⟩
                    ) else (
                      ⟨63,12,false⟩
                    )
                  )
                ) else (
                  if j.val < 848 then (
                    if j.val < 847 then (
                      ⟨64,12,false⟩
                    ) else (
                      ⟨65,12,false⟩
                    )
                  ) else (
                    if j.val < 849 then (
                      ⟨64,18,true⟩
                    ) else (
                      ⟨63,18,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 853 then (
                  if j.val < 851 then (
                    ⟨66,0,false⟩
                  ) else (
                    if j.val < 852 then (
                      ⟨63,18,true⟩
                    ) else (
                      ⟨64,18,false⟩
                    )
                  )
                ) else (
                  if j.val < 855 then (
                    if j.val < 854 then (
                      ⟨65,18,false⟩
                    ) else (
                      ⟨64,12,true⟩
                    )
                  ) else (
                    if j.val < 856 then (
                      ⟨63,12,true⟩
                    ) else (
                      ⟨27,16,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 864 then (
                if j.val < 860 then (
                  if j.val < 858 then (
                    ⟨28,16,false⟩
                  ) else (
                    if j.val < 859 then (
                      ⟨29,16,false⟩
                    ) else (
                      ⟨30,16,false⟩
                    )
                  )
                ) else (
                  if j.val < 862 then (
                    if j.val < 861 then (
                      ⟨64,13,false⟩
                    ) else (
                      ⟨35,10,true⟩
                    )
                  ) else (
                    if j.val < 863 then (
                      ⟨34,10,true⟩
                    ) else (
                      ⟨33,10,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 867 then (
                  if j.val < 865 then (
                    ⟨32,20,true⟩
                  ) else (
                    if j.val < 866 then (
                      ⟨30,20,true⟩
                    ) else (
                      ⟨29,22,false⟩
                    )
                  )
                ) else (
                  if j.val < 869 then (
                    if j.val < 868 then (
                      ⟨31,16,false⟩
                    ) else (
                      ⟨32,16,false⟩
                    )
                  ) else (
                    if j.val < 870 then (
                      ⟨65,13,false⟩
                    ) else (
                      ⟨32,10,true⟩
                    )
                  )
                )
              )
            )
          ) else (
            if j.val < 885 then (
              if j.val < 878 then (
                if j.val < 874 then (
                  if j.val < 872 then (
                    ⟨31,10,true⟩
                  ) else (
                    if j.val < 873 then (
                      ⟨29,20,true⟩
                    ) else (
                      ⟨30,22,false⟩
                    )
                  )
                ) else (
                  if j.val < 876 then (
                    if j.val < 875 then (
                      ⟨32,22,false⟩
                    ) else (
                      ⟨33,16,false⟩
                    )
                  ) else (
                    if j.val < 877 then (
                      ⟨34,16,false⟩
                    ) else (
                      ⟨35,16,false⟩
                    )
                  )
                )
              ) else (
                if j.val < 881 then (
                  if j.val < 879 then (
                    ⟨64,7,true⟩
                  ) else (
                    if j.val < 880 then (
                      ⟨30,10,true⟩
                    ) else (
                      ⟨29,10,true⟩
                    )
                  )
                ) else (
                  if j.val < 883 then (
                    if j.val < 882 then (
                      ⟨28,10,true⟩
                    ) else (
                      ⟨64,19,false⟩
                    )
                  ) else (
                    if j.val < 884 then (
                      ⟨65,19,false⟩
                    ) else (
                      ⟨64,6,true⟩
                    )
                  )
                )
              )
            ) else (
              if j.val < 892 then (
                if j.val < 888 then (
                  if j.val < 886 then (
                    ⟨63,6,true⟩
                  ) else (
                    if j.val < 887 then (
                      ⟨27,10,true⟩
                    ) else (
                      ⟨35,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 890 then (
                    if j.val < 889 then (
                      ⟨34,8,true⟩
                    ) else (
                      ⟨33,8,true⟩
                    )
                  ) else (
                    if j.val < 891 then (
                      ⟨32,14,true⟩
                    ) else (
                      ⟨30,14,true⟩
                    )
                  )
                )
              ) else (
                if j.val < 896 then (
                  if j.val < 894 then (
                    if j.val < 893 then (
                      ⟨32,8,true⟩
                    ) else (
                      ⟨31,8,true⟩
                    )
                  ) else (
                    if j.val < 895 then (
                      ⟨29,14,true⟩
                    ) else (
                      ⟨30,8,true⟩
                    )
                  )
                ) else (
                  if j.val < 898 then (
                    if j.val < 897 then (
                      ⟨29,8,true⟩
                    ) else (
                      ⟨28,8,true⟩
                    )
                  ) else (
                    if j.val < 899 then (
                      ⟨27,8,true⟩
                    ) else (
                      ⟨1,9,true⟩
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

def orbitPatternTransform (d : OrbitDescriptor) (s : Fin 15 → Sign) (q : Fin 15) : Sign :=
  let selected := s (leafMaskPermutation d.permutation q)
  if d.negative then selected.opposite else selected

def orbitPoint (d : OrbitDescriptor) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  if d.negative then fun i => -reorderLeafPoint d.permutation z i
  else reorderLeafPoint d.permutation z

theorem actualSigns_orbitPoint (d : OrbitDescriptor) (z : Fin 4 → ℝ) :
    actualSigns subsetForms (orbitPoint d z) = orbitPatternTransform d (actualSigns subsetForms z) := by
  unfold orbitPoint orbitPatternTransform
  split_ifs <;> simp only [actualSigns_neg, actualSigns_reorderLeafPoint]

end MaxCaterpillar.Frontier.StarCertificate
