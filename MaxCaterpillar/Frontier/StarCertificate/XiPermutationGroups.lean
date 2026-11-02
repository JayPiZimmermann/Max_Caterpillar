import MaxCaterpillar.Frontier.StarCertificate.XiFastSelectors
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def permutationsBeforeMask (P : Fin 16) : List (Fin 120) :=
  if P.val < 8 then (
    if P.val < 4 then (
      if P.val < 2 then (
        if P.val < 1 then (
          [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119]
        ) else (
          [18,19,20,21,22,23]
        )
      ) else (
        if P.val < 3 then (
          [42,43,44,45,46,47]
        ) else (
          [4,5,28,29]
        )
      )
    ) else (
      if P.val < 6 then (
        if P.val < 5 then (
          [66,67,68,69,70,71]
        ) else (
          [10,11,52,53]
        )
      ) else (
        if P.val < 7 then (
          [34,35,58,59]
        ) else (
          [1,7,25,31,49,55]
        )
      )
    )
  ) else (
    if P.val < 12 then (
      if P.val < 10 then (
        if P.val < 9 then (
          [90,91,92,93,94,95]
        ) else (
          [16,17,76,77]
        )
      ) else (
        if P.val < 11 then (
          [40,41,82,83]
        ) else (
          [3,13,27,37,73,79]
        )
      )
    ) else (
      if P.val < 14 then (
        if P.val < 13 then (
          [64,65,88,89]
        ) else (
          [9,15,51,61,75,85]
        )
      ) else (
        if P.val < 15 then (
          [33,39,57,63,81,87]
        ) else (
          [0,2,6,8,12,14,24,26,30,32,36,38,48,50,54,56,60,62,72,74,78,80,84,86]
        )
      )
    )
  )

theorem permutationsBeforeMask_nodup : ∀ P : Fin 16, (permutationsBeforeMask P).Nodup := by decide

theorem permutationsBeforeMask_toFinset : ∀ P : Fin 16,
    (permutationsBeforeMask P).toFinset =
      Finset.univ.filter (fun p => fastCenterBeforeMask p = P) := by decide

theorem sum_permutationsBeforeMask (P : Fin 16) (f : Fin 120 → ℤ) :
    ((permutationsBeforeMask P).map f).sum =
      ∑ p : Fin 120, if fastCenterBeforeMask p = P then f p else 0 := by
  rw [← List.sum_toFinset f (permutationsBeforeMask_nodup P),
    permutationsBeforeMask_toFinset, Finset.sum_filter]

end MaxCaterpillar.Frontier.StarCertificate
