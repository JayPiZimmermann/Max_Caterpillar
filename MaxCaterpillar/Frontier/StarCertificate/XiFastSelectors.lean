import MaxCaterpillar.Frontier.StarCertificate.XiMasks
/-! Generated balanced arithmetic lookups. Closed finite proofs below connect
every entry to the canonical selector tables used by the real semantic proof. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate

def fastChainMask (p : Fin 120) : Fin 4 → ℕ :=
  if p.val < 60 then (
    if p.val < 30 then (
      if p.val < 15 then (
        if p.val < 7 then (
          if p.val < 3 then (
            if p.val < 1 then (
              ![1, 3, 7, 15]
            ) else (
              if p.val < 2 then (
                ![1, 3, 7, 8]
              ) else (
                ![1, 3, 11, 15]
              )
            )
          ) else (
            if p.val < 5 then (
              if p.val < 4 then (
                ![1, 3, 11, 4]
              ) else (
                ![1, 3, 12, 8]
              )
            ) else (
              if p.val < 6 then (
                ![1, 3, 12, 4]
              ) else (
                ![1, 5, 7, 15]
              )
            )
          )
        ) else (
          if p.val < 11 then (
            if p.val < 9 then (
              if p.val < 8 then (
                ![1, 5, 7, 8]
              ) else (
                ![1, 5, 13, 15]
              )
            ) else (
              if p.val < 10 then (
                ![1, 5, 13, 2]
              ) else (
                ![1, 5, 10, 8]
              )
            )
          ) else (
            if p.val < 13 then (
              if p.val < 12 then (
                ![1, 5, 10, 2]
              ) else (
                ![1, 9, 11, 15]
              )
            ) else (
              if p.val < 14 then (
                ![1, 9, 11, 4]
              ) else (
                ![1, 9, 13, 15]
              )
            )
          )
        )
      ) else (
        if p.val < 22 then (
          if p.val < 18 then (
            if p.val < 16 then (
              ![1, 9, 13, 2]
            ) else (
              if p.val < 17 then (
                ![1, 9, 6, 4]
              ) else (
                ![1, 9, 6, 2]
              )
            )
          ) else (
            if p.val < 20 then (
              if p.val < 19 then (
                ![1, 14, 12, 8]
              ) else (
                ![1, 14, 12, 4]
              )
            ) else (
              if p.val < 21 then (
                ![1, 14, 10, 8]
              ) else (
                ![1, 14, 10, 2]
              )
            )
          )
        ) else (
          if p.val < 26 then (
            if p.val < 24 then (
              if p.val < 23 then (
                ![1, 14, 6, 4]
              ) else (
                ![1, 14, 6, 2]
              )
            ) else (
              if p.val < 25 then (
                ![2, 3, 7, 15]
              ) else (
                ![2, 3, 7, 8]
              )
            )
          ) else (
            if p.val < 28 then (
              if p.val < 27 then (
                ![2, 3, 11, 15]
              ) else (
                ![2, 3, 11, 4]
              )
            ) else (
              if p.val < 29 then (
                ![2, 3, 12, 8]
              ) else (
                ![2, 3, 12, 4]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 45 then (
        if p.val < 37 then (
          if p.val < 33 then (
            if p.val < 31 then (
              ![2, 6, 7, 15]
            ) else (
              if p.val < 32 then (
                ![2, 6, 7, 8]
              ) else (
                ![2, 6, 14, 15]
              )
            )
          ) else (
            if p.val < 35 then (
              if p.val < 34 then (
                ![2, 6, 14, 1]
              ) else (
                ![2, 6, 9, 8]
              )
            ) else (
              if p.val < 36 then (
                ![2, 6, 9, 1]
              ) else (
                ![2, 10, 11, 15]
              )
            )
          )
        ) else (
          if p.val < 41 then (
            if p.val < 39 then (
              if p.val < 38 then (
                ![2, 10, 11, 4]
              ) else (
                ![2, 10, 14, 15]
              )
            ) else (
              if p.val < 40 then (
                ![2, 10, 14, 1]
              ) else (
                ![2, 10, 5, 4]
              )
            )
          ) else (
            if p.val < 43 then (
              if p.val < 42 then (
                ![2, 10, 5, 1]
              ) else (
                ![2, 13, 12, 8]
              )
            ) else (
              if p.val < 44 then (
                ![2, 13, 12, 4]
              ) else (
                ![2, 13, 9, 8]
              )
            )
          )
        )
      ) else (
        if p.val < 52 then (
          if p.val < 48 then (
            if p.val < 46 then (
              ![2, 13, 9, 1]
            ) else (
              if p.val < 47 then (
                ![2, 13, 5, 4]
              ) else (
                ![2, 13, 5, 1]
              )
            )
          ) else (
            if p.val < 50 then (
              if p.val < 49 then (
                ![4, 5, 7, 15]
              ) else (
                ![4, 5, 7, 8]
              )
            ) else (
              if p.val < 51 then (
                ![4, 5, 13, 15]
              ) else (
                ![4, 5, 13, 2]
              )
            )
          )
        ) else (
          if p.val < 56 then (
            if p.val < 54 then (
              if p.val < 53 then (
                ![4, 5, 10, 8]
              ) else (
                ![4, 5, 10, 2]
              )
            ) else (
              if p.val < 55 then (
                ![4, 6, 7, 15]
              ) else (
                ![4, 6, 7, 8]
              )
            )
          ) else (
            if p.val < 58 then (
              if p.val < 57 then (
                ![4, 6, 14, 15]
              ) else (
                ![4, 6, 14, 1]
              )
            ) else (
              if p.val < 59 then (
                ![4, 6, 9, 8]
              ) else (
                ![4, 6, 9, 1]
              )
            )
          )
        )
      )
    )
  ) else (
    if p.val < 90 then (
      if p.val < 75 then (
        if p.val < 67 then (
          if p.val < 63 then (
            if p.val < 61 then (
              ![4, 12, 13, 15]
            ) else (
              if p.val < 62 then (
                ![4, 12, 13, 2]
              ) else (
                ![4, 12, 14, 15]
              )
            )
          ) else (
            if p.val < 65 then (
              if p.val < 64 then (
                ![4, 12, 14, 1]
              ) else (
                ![4, 12, 3, 2]
              )
            ) else (
              if p.val < 66 then (
                ![4, 12, 3, 1]
              ) else (
                ![4, 11, 10, 8]
              )
            )
          )
        ) else (
          if p.val < 71 then (
            if p.val < 69 then (
              if p.val < 68 then (
                ![4, 11, 10, 2]
              ) else (
                ![4, 11, 9, 8]
              )
            ) else (
              if p.val < 70 then (
                ![4, 11, 9, 1]
              ) else (
                ![4, 11, 3, 2]
              )
            )
          ) else (
            if p.val < 73 then (
              if p.val < 72 then (
                ![4, 11, 3, 1]
              ) else (
                ![8, 9, 11, 15]
              )
            ) else (
              if p.val < 74 then (
                ![8, 9, 11, 4]
              ) else (
                ![8, 9, 13, 15]
              )
            )
          )
        )
      ) else (
        if p.val < 82 then (
          if p.val < 78 then (
            if p.val < 76 then (
              ![8, 9, 13, 2]
            ) else (
              if p.val < 77 then (
                ![8, 9, 6, 4]
              ) else (
                ![8, 9, 6, 2]
              )
            )
          ) else (
            if p.val < 80 then (
              if p.val < 79 then (
                ![8, 10, 11, 15]
              ) else (
                ![8, 10, 11, 4]
              )
            ) else (
              if p.val < 81 then (
                ![8, 10, 14, 15]
              ) else (
                ![8, 10, 14, 1]
              )
            )
          )
        ) else (
          if p.val < 86 then (
            if p.val < 84 then (
              if p.val < 83 then (
                ![8, 10, 5, 4]
              ) else (
                ![8, 10, 5, 1]
              )
            ) else (
              if p.val < 85 then (
                ![8, 12, 13, 15]
              ) else (
                ![8, 12, 13, 2]
              )
            )
          ) else (
            if p.val < 88 then (
              if p.val < 87 then (
                ![8, 12, 14, 15]
              ) else (
                ![8, 12, 14, 1]
              )
            ) else (
              if p.val < 89 then (
                ![8, 12, 3, 2]
              ) else (
                ![8, 12, 3, 1]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 105 then (
        if p.val < 97 then (
          if p.val < 93 then (
            if p.val < 91 then (
              ![8, 7, 6, 4]
            ) else (
              if p.val < 92 then (
                ![8, 7, 6, 2]
              ) else (
                ![8, 7, 5, 4]
              )
            )
          ) else (
            if p.val < 95 then (
              if p.val < 94 then (
                ![8, 7, 5, 1]
              ) else (
                ![8, 7, 3, 2]
              )
            ) else (
              if p.val < 96 then (
                ![8, 7, 3, 1]
              ) else (
                ![15, 14, 12, 8]
              )
            )
          )
        ) else (
          if p.val < 101 then (
            if p.val < 99 then (
              if p.val < 98 then (
                ![15, 14, 12, 4]
              ) else (
                ![15, 14, 10, 8]
              )
            ) else (
              if p.val < 100 then (
                ![15, 14, 10, 2]
              ) else (
                ![15, 14, 6, 4]
              )
            )
          ) else (
            if p.val < 103 then (
              if p.val < 102 then (
                ![15, 14, 6, 2]
              ) else (
                ![15, 13, 12, 8]
              )
            ) else (
              if p.val < 104 then (
                ![15, 13, 12, 4]
              ) else (
                ![15, 13, 9, 8]
              )
            )
          )
        )
      ) else (
        if p.val < 112 then (
          if p.val < 108 then (
            if p.val < 106 then (
              ![15, 13, 9, 1]
            ) else (
              if p.val < 107 then (
                ![15, 13, 5, 4]
              ) else (
                ![15, 13, 5, 1]
              )
            )
          ) else (
            if p.val < 110 then (
              if p.val < 109 then (
                ![15, 11, 10, 8]
              ) else (
                ![15, 11, 10, 2]
              )
            ) else (
              if p.val < 111 then (
                ![15, 11, 9, 8]
              ) else (
                ![15, 11, 9, 1]
              )
            )
          )
        ) else (
          if p.val < 116 then (
            if p.val < 114 then (
              if p.val < 113 then (
                ![15, 11, 3, 2]
              ) else (
                ![15, 11, 3, 1]
              )
            ) else (
              if p.val < 115 then (
                ![15, 7, 6, 4]
              ) else (
                ![15, 7, 6, 2]
              )
            )
          ) else (
            if p.val < 118 then (
              if p.val < 117 then (
                ![15, 7, 5, 4]
              ) else (
                ![15, 7, 5, 1]
              )
            ) else (
              if p.val < 119 then (
                ![15, 7, 3, 2]
              ) else (
                ![15, 7, 3, 1]
              )
            )
          )
        )
      )
    )
  )

theorem fastChainMask_eq : ∀ (p : Fin 120) (j : Fin 4), fastChainMask p j = chainMask p j := by decide

def fastChainNegative (p : Fin 120) : Fin 4 → Bool :=
  if p.val < 60 then (
    if p.val < 30 then (
      if p.val < 15 then (
        if p.val < 7 then (
          if p.val < 3 then (
            if p.val < 1 then (
              ![false, false, false, false]
            ) else (
              if p.val < 2 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            )
          ) else (
            if p.val < 5 then (
              if p.val < 4 then (
                ![false, false, false, true]
              ) else (
                ![false, false, true, true]
              )
            ) else (
              if p.val < 6 then (
                ![false, false, true, true]
              ) else (
                ![false, false, false, false]
              )
            )
          )
        ) else (
          if p.val < 11 then (
            if p.val < 9 then (
              if p.val < 8 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            ) else (
              if p.val < 10 then (
                ![false, false, false, true]
              ) else (
                ![false, false, true, true]
              )
            )
          ) else (
            if p.val < 13 then (
              if p.val < 12 then (
                ![false, false, true, true]
              ) else (
                ![false, false, false, false]
              )
            ) else (
              if p.val < 14 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            )
          )
        )
      ) else (
        if p.val < 22 then (
          if p.val < 18 then (
            if p.val < 16 then (
              ![false, false, false, true]
            ) else (
              if p.val < 17 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            )
          ) else (
            if p.val < 20 then (
              if p.val < 19 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            ) else (
              if p.val < 21 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            )
          )
        ) else (
          if p.val < 26 then (
            if p.val < 24 then (
              if p.val < 23 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            ) else (
              if p.val < 25 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            )
          ) else (
            if p.val < 28 then (
              if p.val < 27 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            ) else (
              if p.val < 29 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 45 then (
        if p.val < 37 then (
          if p.val < 33 then (
            if p.val < 31 then (
              ![false, false, false, false]
            ) else (
              if p.val < 32 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            )
          ) else (
            if p.val < 35 then (
              if p.val < 34 then (
                ![false, false, false, true]
              ) else (
                ![false, false, true, true]
              )
            ) else (
              if p.val < 36 then (
                ![false, false, true, true]
              ) else (
                ![false, false, false, false]
              )
            )
          )
        ) else (
          if p.val < 41 then (
            if p.val < 39 then (
              if p.val < 38 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            ) else (
              if p.val < 40 then (
                ![false, false, false, true]
              ) else (
                ![false, false, true, true]
              )
            )
          ) else (
            if p.val < 43 then (
              if p.val < 42 then (
                ![false, false, true, true]
              ) else (
                ![false, true, true, true]
              )
            ) else (
              if p.val < 44 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            )
          )
        )
      ) else (
        if p.val < 52 then (
          if p.val < 48 then (
            if p.val < 46 then (
              ![false, true, true, true]
            ) else (
              if p.val < 47 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            )
          ) else (
            if p.val < 50 then (
              if p.val < 49 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            ) else (
              if p.val < 51 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            )
          )
        ) else (
          if p.val < 56 then (
            if p.val < 54 then (
              if p.val < 53 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            ) else (
              if p.val < 55 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            )
          ) else (
            if p.val < 58 then (
              if p.val < 57 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            ) else (
              if p.val < 59 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            )
          )
        )
      )
    )
  ) else (
    if p.val < 90 then (
      if p.val < 75 then (
        if p.val < 67 then (
          if p.val < 63 then (
            if p.val < 61 then (
              ![false, false, false, false]
            ) else (
              if p.val < 62 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            )
          ) else (
            if p.val < 65 then (
              if p.val < 64 then (
                ![false, false, false, true]
              ) else (
                ![false, false, true, true]
              )
            ) else (
              if p.val < 66 then (
                ![false, false, true, true]
              ) else (
                ![false, true, true, true]
              )
            )
          )
        ) else (
          if p.val < 71 then (
            if p.val < 69 then (
              if p.val < 68 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            ) else (
              if p.val < 70 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            )
          ) else (
            if p.val < 73 then (
              if p.val < 72 then (
                ![false, true, true, true]
              ) else (
                ![false, false, false, false]
              )
            ) else (
              if p.val < 74 then (
                ![false, false, false, true]
              ) else (
                ![false, false, false, false]
              )
            )
          )
        )
      ) else (
        if p.val < 82 then (
          if p.val < 78 then (
            if p.val < 76 then (
              ![false, false, false, true]
            ) else (
              if p.val < 77 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            )
          ) else (
            if p.val < 80 then (
              if p.val < 79 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            ) else (
              if p.val < 81 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            )
          )
        ) else (
          if p.val < 86 then (
            if p.val < 84 then (
              if p.val < 83 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            ) else (
              if p.val < 85 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            )
          ) else (
            if p.val < 88 then (
              if p.val < 87 then (
                ![false, false, false, false]
              ) else (
                ![false, false, false, true]
              )
            ) else (
              if p.val < 89 then (
                ![false, false, true, true]
              ) else (
                ![false, false, true, true]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 105 then (
        if p.val < 97 then (
          if p.val < 93 then (
            if p.val < 91 then (
              ![false, true, true, true]
            ) else (
              if p.val < 92 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            )
          ) else (
            if p.val < 95 then (
              if p.val < 94 then (
                ![false, true, true, true]
              ) else (
                ![false, true, true, true]
              )
            ) else (
              if p.val < 96 then (
                ![false, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          )
        ) else (
          if p.val < 101 then (
            if p.val < 99 then (
              if p.val < 98 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            ) else (
              if p.val < 100 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          ) else (
            if p.val < 103 then (
              if p.val < 102 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            ) else (
              if p.val < 104 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          )
        )
      ) else (
        if p.val < 112 then (
          if p.val < 108 then (
            if p.val < 106 then (
              ![true, true, true, true]
            ) else (
              if p.val < 107 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          ) else (
            if p.val < 110 then (
              if p.val < 109 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            ) else (
              if p.val < 111 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          )
        ) else (
          if p.val < 116 then (
            if p.val < 114 then (
              if p.val < 113 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            ) else (
              if p.val < 115 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          ) else (
            if p.val < 118 then (
              if p.val < 117 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            ) else (
              if p.val < 119 then (
                ![true, true, true, true]
              ) else (
                ![true, true, true, true]
              )
            )
          )
        )
      )
    )
  )

theorem fastChainNegative_eq : ∀ (p : Fin 120) (j : Fin 4), fastChainNegative p j = chainNegative p j := by decide

def fastCoarseMask (p : Fin 120) : Fin 10 → ℕ :=
  if p.val < 60 then (
    if p.val < 30 then (
      if p.val < 15 then (
        if p.val < 7 then (
          if p.val < 3 then (
            if p.val < 1 then (
              ![1, 15, 3, 9, 14, 6, 10, 13, 12, 7]
            ) else (
              if p.val < 2 then (
                ![1, 8, 3, 14, 9, 6, 13, 10, 11, 7]
              ) else (
                ![1, 15, 3, 5, 14, 10, 6, 13, 12, 11]
              )
            )
          ) else (
            if p.val < 5 then (
              if p.val < 4 then (
                ![1, 4, 3, 14, 5, 10, 13, 6, 7, 11]
              ) else (
                ![1, 8, 3, 5, 9, 13, 6, 10, 11, 12]
              )
            ) else (
              if p.val < 6 then (
                ![1, 4, 3, 9, 5, 13, 10, 6, 7, 12]
              ) else (
                ![1, 15, 5, 9, 14, 6, 12, 11, 10, 7]
              )
            )
          )
        ) else (
          if p.val < 11 then (
            if p.val < 9 then (
              if p.val < 8 then (
                ![1, 8, 5, 14, 9, 6, 11, 12, 13, 7]
              ) else (
                ![1, 15, 5, 3, 14, 12, 6, 11, 10, 13]
              )
            ) else (
              if p.val < 10 then (
                ![1, 2, 5, 14, 3, 12, 11, 6, 7, 13]
              ) else (
                ![1, 8, 5, 3, 9, 11, 6, 12, 13, 10]
              )
            )
          ) else (
            if p.val < 13 then (
              if p.val < 12 then (
                ![1, 2, 5, 9, 3, 11, 12, 6, 7, 10]
              ) else (
                ![1, 15, 9, 5, 14, 10, 12, 7, 6, 11]
              )
            ) else (
              if p.val < 14 then (
                ![1, 4, 9, 14, 5, 10, 7, 12, 13, 11]
              ) else (
                ![1, 15, 9, 3, 14, 12, 10, 7, 6, 13]
              )
            )
          )
        )
      ) else (
        if p.val < 22 then (
          if p.val < 18 then (
            if p.val < 16 then (
              ![1, 2, 9, 14, 3, 12, 7, 10, 11, 13]
            ) else (
              if p.val < 17 then (
                ![1, 4, 9, 3, 5, 7, 10, 12, 13, 6]
              ) else (
                ![1, 2, 9, 5, 3, 7, 12, 10, 11, 6]
              )
            )
          ) else (
            if p.val < 20 then (
              if p.val < 19 then (
                ![1, 8, 14, 5, 9, 13, 11, 7, 6, 12]
              ) else (
                ![1, 4, 14, 9, 5, 13, 7, 11, 10, 12]
              )
            ) else (
              if p.val < 21 then (
                ![1, 8, 14, 3, 9, 11, 13, 7, 6, 10]
              ) else (
                ![1, 2, 14, 9, 3, 11, 7, 13, 12, 10]
              )
            )
          )
        ) else (
          if p.val < 26 then (
            if p.val < 24 then (
              if p.val < 23 then (
                ![1, 4, 14, 3, 5, 7, 13, 11, 10, 6]
              ) else (
                ![1, 2, 14, 5, 3, 7, 11, 13, 12, 6]
              )
            ) else (
              if p.val < 25 then (
                ![2, 15, 3, 10, 13, 5, 9, 14, 12, 7]
              ) else (
                ![2, 8, 3, 13, 10, 5, 14, 9, 11, 7]
              )
            )
          ) else (
            if p.val < 28 then (
              if p.val < 27 then (
                ![2, 15, 3, 6, 13, 9, 5, 14, 12, 11]
              ) else (
                ![2, 4, 3, 13, 6, 9, 14, 5, 7, 11]
              )
            ) else (
              if p.val < 29 then (
                ![2, 8, 3, 6, 10, 14, 5, 9, 11, 12]
              ) else (
                ![2, 4, 3, 10, 6, 14, 9, 5, 7, 12]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 45 then (
        if p.val < 37 then (
          if p.val < 33 then (
            if p.val < 31 then (
              ![2, 15, 6, 10, 13, 5, 12, 11, 9, 7]
            ) else (
              if p.val < 32 then (
                ![2, 8, 6, 13, 10, 5, 11, 12, 14, 7]
              ) else (
                ![2, 15, 6, 3, 13, 12, 5, 11, 9, 14]
              )
            )
          ) else (
            if p.val < 35 then (
              if p.val < 34 then (
                ![2, 1, 6, 13, 3, 12, 11, 5, 7, 14]
              ) else (
                ![2, 8, 6, 3, 10, 11, 5, 12, 14, 9]
              )
            ) else (
              if p.val < 36 then (
                ![2, 1, 6, 10, 3, 11, 12, 5, 7, 9]
              ) else (
                ![2, 15, 10, 6, 13, 9, 12, 7, 5, 11]
              )
            )
          )
        ) else (
          if p.val < 41 then (
            if p.val < 39 then (
              if p.val < 38 then (
                ![2, 4, 10, 13, 6, 9, 7, 12, 14, 11]
              ) else (
                ![2, 15, 10, 3, 13, 12, 9, 7, 5, 14]
              )
            ) else (
              if p.val < 40 then (
                ![2, 1, 10, 13, 3, 12, 7, 9, 11, 14]
              ) else (
                ![2, 4, 10, 3, 6, 7, 9, 12, 14, 5]
              )
            )
          ) else (
            if p.val < 43 then (
              if p.val < 42 then (
                ![2, 1, 10, 6, 3, 7, 12, 9, 11, 5]
              ) else (
                ![2, 8, 13, 6, 10, 14, 11, 7, 5, 12]
              )
            ) else (
              if p.val < 44 then (
                ![2, 4, 13, 10, 6, 14, 7, 11, 9, 12]
              ) else (
                ![2, 8, 13, 3, 10, 11, 14, 7, 5, 9]
              )
            )
          )
        )
      ) else (
        if p.val < 52 then (
          if p.val < 48 then (
            if p.val < 46 then (
              ![2, 1, 13, 10, 3, 11, 7, 14, 12, 9]
            ) else (
              if p.val < 47 then (
                ![2, 4, 13, 3, 6, 7, 14, 11, 9, 5]
              ) else (
                ![2, 1, 13, 6, 3, 7, 11, 14, 12, 5]
              )
            )
          ) else (
            if p.val < 50 then (
              if p.val < 49 then (
                ![4, 15, 5, 12, 11, 3, 9, 14, 10, 7]
              ) else (
                ![4, 8, 5, 11, 12, 3, 14, 9, 13, 7]
              )
            ) else (
              if p.val < 51 then (
                ![4, 15, 5, 6, 11, 9, 3, 14, 10, 13]
              ) else (
                ![4, 2, 5, 11, 6, 9, 14, 3, 7, 13]
              )
            )
          )
        ) else (
          if p.val < 56 then (
            if p.val < 54 then (
              if p.val < 53 then (
                ![4, 8, 5, 6, 12, 14, 3, 9, 13, 10]
              ) else (
                ![4, 2, 5, 12, 6, 14, 9, 3, 7, 10]
              )
            ) else (
              if p.val < 55 then (
                ![4, 15, 6, 12, 11, 3, 10, 13, 9, 7]
              ) else (
                ![4, 8, 6, 11, 12, 3, 13, 10, 14, 7]
              )
            )
          ) else (
            if p.val < 58 then (
              if p.val < 57 then (
                ![4, 15, 6, 5, 11, 10, 3, 13, 9, 14]
              ) else (
                ![4, 1, 6, 11, 5, 10, 13, 3, 7, 14]
              )
            ) else (
              if p.val < 59 then (
                ![4, 8, 6, 5, 12, 13, 3, 10, 14, 9]
              ) else (
                ![4, 1, 6, 12, 5, 13, 10, 3, 7, 9]
              )
            )
          )
        )
      )
    )
  ) else (
    if p.val < 90 then (
      if p.val < 75 then (
        if p.val < 67 then (
          if p.val < 63 then (
            if p.val < 61 then (
              ![4, 15, 12, 6, 11, 9, 10, 7, 3, 13]
            ) else (
              if p.val < 62 then (
                ![4, 2, 12, 11, 6, 9, 7, 10, 14, 13]
              ) else (
                ![4, 15, 12, 5, 11, 10, 9, 7, 3, 14]
              )
            )
          ) else (
            if p.val < 65 then (
              if p.val < 64 then (
                ![4, 1, 12, 11, 5, 10, 7, 9, 13, 14]
              ) else (
                ![4, 2, 12, 5, 6, 7, 9, 10, 14, 3]
              )
            ) else (
              if p.val < 66 then (
                ![4, 1, 12, 6, 5, 7, 10, 9, 13, 3]
              ) else (
                ![4, 8, 11, 6, 12, 14, 13, 7, 3, 10]
              )
            )
          )
        ) else (
          if p.val < 71 then (
            if p.val < 69 then (
              if p.val < 68 then (
                ![4, 2, 11, 12, 6, 14, 7, 13, 9, 10]
              ) else (
                ![4, 8, 11, 5, 12, 13, 14, 7, 3, 9]
              )
            ) else (
              if p.val < 70 then (
                ![4, 1, 11, 12, 5, 13, 7, 14, 10, 9]
              ) else (
                ![4, 2, 11, 5, 6, 7, 14, 13, 9, 3]
              )
            )
          ) else (
            if p.val < 73 then (
              if p.val < 72 then (
                ![4, 1, 11, 6, 5, 7, 13, 14, 10, 3]
              ) else (
                ![8, 15, 9, 12, 7, 3, 5, 14, 6, 11]
              )
            ) else (
              if p.val < 74 then (
                ![8, 4, 9, 7, 12, 3, 14, 5, 13, 11]
              ) else (
                ![8, 15, 9, 10, 7, 5, 3, 14, 6, 13]
              )
            )
          )
        )
      ) else (
        if p.val < 82 then (
          if p.val < 78 then (
            if p.val < 76 then (
              ![8, 2, 9, 7, 10, 5, 14, 3, 11, 13]
            ) else (
              if p.val < 77 then (
                ![8, 4, 9, 10, 12, 14, 3, 5, 13, 6]
              ) else (
                ![8, 2, 9, 12, 10, 14, 5, 3, 11, 6]
              )
            )
          ) else (
            if p.val < 80 then (
              if p.val < 79 then (
                ![8, 15, 10, 12, 7, 3, 6, 13, 5, 11]
              ) else (
                ![8, 4, 10, 7, 12, 3, 13, 6, 14, 11]
              )
            ) else (
              if p.val < 81 then (
                ![8, 15, 10, 9, 7, 6, 3, 13, 5, 14]
              ) else (
                ![8, 1, 10, 7, 9, 6, 13, 3, 11, 14]
              )
            )
          )
        ) else (
          if p.val < 86 then (
            if p.val < 84 then (
              if p.val < 83 then (
                ![8, 4, 10, 9, 12, 13, 3, 6, 14, 5]
              ) else (
                ![8, 1, 10, 12, 9, 13, 6, 3, 11, 5]
              )
            ) else (
              if p.val < 85 then (
                ![8, 15, 12, 10, 7, 5, 6, 11, 3, 13]
              ) else (
                ![8, 2, 12, 7, 10, 5, 11, 6, 14, 13]
              )
            )
          ) else (
            if p.val < 88 then (
              if p.val < 87 then (
                ![8, 15, 12, 9, 7, 6, 5, 11, 3, 14]
              ) else (
                ![8, 1, 12, 7, 9, 6, 11, 5, 13, 14]
              )
            ) else (
              if p.val < 89 then (
                ![8, 2, 12, 9, 10, 11, 5, 6, 14, 3]
              ) else (
                ![8, 1, 12, 10, 9, 11, 6, 5, 13, 3]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 105 then (
        if p.val < 97 then (
          if p.val < 93 then (
            if p.val < 91 then (
              ![8, 4, 7, 10, 12, 14, 13, 11, 3, 6]
            ) else (
              if p.val < 92 then (
                ![8, 2, 7, 12, 10, 14, 11, 13, 5, 6]
              ) else (
                ![8, 4, 7, 9, 12, 13, 14, 11, 3, 5]
              )
            )
          ) else (
            if p.val < 95 then (
              if p.val < 94 then (
                ![8, 1, 7, 12, 9, 13, 11, 14, 6, 5]
              ) else (
                ![8, 2, 7, 9, 10, 11, 14, 13, 5, 3]
              )
            ) else (
              if p.val < 96 then (
                ![8, 1, 7, 10, 9, 11, 13, 14, 6, 3]
              ) else (
                ![15, 8, 14, 11, 7, 3, 5, 9, 6, 12]
              )
            )
          )
        ) else (
          if p.val < 101 then (
            if p.val < 99 then (
              if p.val < 98 then (
                ![15, 4, 14, 7, 11, 3, 9, 5, 10, 12]
              ) else (
                ![15, 8, 14, 13, 7, 5, 3, 9, 6, 10]
              )
            ) else (
              if p.val < 100 then (
                ![15, 2, 14, 7, 13, 5, 9, 3, 12, 10]
              ) else (
                ![15, 4, 14, 13, 11, 9, 3, 5, 10, 6]
              )
            )
          ) else (
            if p.val < 103 then (
              if p.val < 102 then (
                ![15, 2, 14, 11, 13, 9, 5, 3, 12, 6]
              ) else (
                ![15, 8, 13, 11, 7, 3, 6, 10, 5, 12]
              )
            ) else (
              if p.val < 104 then (
                ![15, 4, 13, 7, 11, 3, 10, 6, 9, 12]
              ) else (
                ![15, 8, 13, 14, 7, 6, 3, 10, 5, 9]
              )
            )
          )
        )
      ) else (
        if p.val < 112 then (
          if p.val < 108 then (
            if p.val < 106 then (
              ![15, 1, 13, 7, 14, 6, 10, 3, 12, 9]
            ) else (
              if p.val < 107 then (
                ![15, 4, 13, 14, 11, 10, 3, 6, 9, 5]
              ) else (
                ![15, 1, 13, 11, 14, 10, 6, 3, 12, 5]
              )
            )
          ) else (
            if p.val < 110 then (
              if p.val < 109 then (
                ![15, 8, 11, 13, 7, 5, 6, 12, 3, 10]
              ) else (
                ![15, 2, 11, 7, 13, 5, 12, 6, 9, 10]
              )
            ) else (
              if p.val < 111 then (
                ![15, 8, 11, 14, 7, 6, 5, 12, 3, 9]
              ) else (
                ![15, 1, 11, 7, 14, 6, 12, 5, 10, 9]
              )
            )
          )
        ) else (
          if p.val < 116 then (
            if p.val < 114 then (
              if p.val < 113 then (
                ![15, 2, 11, 14, 13, 12, 5, 6, 9, 3]
              ) else (
                ![15, 1, 11, 13, 14, 12, 6, 5, 10, 3]
              )
            ) else (
              if p.val < 115 then (
                ![15, 4, 7, 13, 11, 9, 10, 12, 3, 6]
              ) else (
                ![15, 2, 7, 11, 13, 9, 12, 10, 5, 6]
              )
            )
          ) else (
            if p.val < 118 then (
              if p.val < 117 then (
                ![15, 4, 7, 14, 11, 10, 9, 12, 3, 5]
              ) else (
                ![15, 1, 7, 11, 14, 10, 12, 9, 6, 5]
              )
            ) else (
              if p.val < 119 then (
                ![15, 2, 7, 14, 13, 12, 9, 10, 5, 3]
              ) else (
                ![15, 1, 7, 13, 14, 12, 10, 9, 6, 3]
              )
            )
          )
        )
      )
    )
  )

theorem fastCoarseMask_eq : ∀ (p : Fin 120) (j : Fin 10), fastCoarseMask p j = coarseMask p j := by decide

def fastCoarseNegative (p : Fin 120) : Fin 10 → Bool :=
  if p.val < 60 then (
    if p.val < 30 then (
      if p.val < 15 then (
        if p.val < 7 then (
          if p.val < 3 then (
            if p.val < 1 then (
              ![false, false, false, false, true, false, false, true, false, true]
            ) else (
              if p.val < 2 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          ) else (
            if p.val < 5 then (
              if p.val < 4 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            ) else (
              if p.val < 6 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          )
        ) else (
          if p.val < 11 then (
            if p.val < 9 then (
              if p.val < 8 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            ) else (
              if p.val < 10 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          ) else (
            if p.val < 13 then (
              if p.val < 12 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            ) else (
              if p.val < 14 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          )
        )
      ) else (
        if p.val < 22 then (
          if p.val < 18 then (
            if p.val < 16 then (
              ![false, true, false, true, false, false, true, false, true, true]
            ) else (
              if p.val < 17 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          ) else (
            if p.val < 20 then (
              if p.val < 19 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            ) else (
              if p.val < 21 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            )
          )
        ) else (
          if p.val < 26 then (
            if p.val < 24 then (
              if p.val < 23 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            ) else (
              if p.val < 25 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            )
          ) else (
            if p.val < 28 then (
              if p.val < 27 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            ) else (
              if p.val < 29 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 45 then (
        if p.val < 37 then (
          if p.val < 33 then (
            if p.val < 31 then (
              ![false, false, false, false, true, false, false, true, false, true]
            ) else (
              if p.val < 32 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          ) else (
            if p.val < 35 then (
              if p.val < 34 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            ) else (
              if p.val < 36 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          )
        ) else (
          if p.val < 41 then (
            if p.val < 39 then (
              if p.val < 38 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            ) else (
              if p.val < 40 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          ) else (
            if p.val < 43 then (
              if p.val < 42 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            ) else (
              if p.val < 44 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            )
          )
        )
      ) else (
        if p.val < 52 then (
          if p.val < 48 then (
            if p.val < 46 then (
              ![false, true, true, false, false, true, true, true, false, false]
            ) else (
              if p.val < 47 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            )
          ) else (
            if p.val < 50 then (
              if p.val < 49 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            ) else (
              if p.val < 51 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            )
          )
        ) else (
          if p.val < 56 then (
            if p.val < 54 then (
              if p.val < 53 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            ) else (
              if p.val < 55 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            )
          ) else (
            if p.val < 58 then (
              if p.val < 57 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            ) else (
              if p.val < 59 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          )
        )
      )
    )
  ) else (
    if p.val < 90 then (
      if p.val < 75 then (
        if p.val < 67 then (
          if p.val < 63 then (
            if p.val < 61 then (
              ![false, false, false, false, true, false, false, true, false, true]
            ) else (
              if p.val < 62 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          ) else (
            if p.val < 65 then (
              if p.val < 64 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            ) else (
              if p.val < 66 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            )
          )
        ) else (
          if p.val < 71 then (
            if p.val < 69 then (
              if p.val < 68 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            ) else (
              if p.val < 70 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            )
          ) else (
            if p.val < 73 then (
              if p.val < 72 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            ) else (
              if p.val < 74 then (
                ![false, true, false, true, false, false, true, false, true, true]
              ) else (
                ![false, false, false, false, true, false, false, true, false, true]
              )
            )
          )
        )
      ) else (
        if p.val < 82 then (
          if p.val < 78 then (
            if p.val < 76 then (
              ![false, true, false, true, false, false, true, false, true, true]
            ) else (
              if p.val < 77 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          ) else (
            if p.val < 80 then (
              if p.val < 79 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            ) else (
              if p.val < 81 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            )
          )
        ) else (
          if p.val < 86 then (
            if p.val < 84 then (
              if p.val < 83 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            ) else (
              if p.val < 85 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            )
          ) else (
            if p.val < 88 then (
              if p.val < 87 then (
                ![false, false, false, false, true, false, false, true, false, true]
              ) else (
                ![false, true, false, true, false, false, true, false, true, true]
              )
            ) else (
              if p.val < 89 then (
                ![false, true, false, false, false, true, false, false, true, false]
              ) else (
                ![false, true, false, false, false, true, false, false, true, false]
              )
            )
          )
        )
      )
    ) else (
      if p.val < 105 then (
        if p.val < 97 then (
          if p.val < 93 then (
            if p.val < 91 then (
              ![false, true, true, false, false, true, true, true, false, false]
            ) else (
              if p.val < 92 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            )
          ) else (
            if p.val < 95 then (
              if p.val < 94 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![false, true, true, false, false, true, true, true, false, false]
              )
            ) else (
              if p.val < 96 then (
                ![false, true, true, false, false, true, true, true, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          )
        ) else (
          if p.val < 101 then (
            if p.val < 99 then (
              if p.val < 98 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            ) else (
              if p.val < 100 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          ) else (
            if p.val < 103 then (
              if p.val < 102 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            ) else (
              if p.val < 104 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          )
        )
      ) else (
        if p.val < 112 then (
          if p.val < 108 then (
            if p.val < 106 then (
              ![true, true, true, true, true, false, false, false, false, false]
            ) else (
              if p.val < 107 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          ) else (
            if p.val < 110 then (
              if p.val < 109 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            ) else (
              if p.val < 111 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          )
        ) else (
          if p.val < 116 then (
            if p.val < 114 then (
              if p.val < 113 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            ) else (
              if p.val < 115 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          ) else (
            if p.val < 118 then (
              if p.val < 117 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            ) else (
              if p.val < 119 then (
                ![true, true, true, true, true, false, false, false, false, false]
              ) else (
                ![true, true, true, true, true, false, false, false, false, false]
              )
            )
          )
        )
      )
    )
  )

theorem fastCoarseNegative_eq : ∀ (p : Fin 120) (j : Fin 10), fastCoarseNegative p j = coarseNegative p j := by decide

def fastCenterBeforeMask (p : Fin 120) : Fin 16 :=
  if p.val < 60 then (
    if p.val < 30 then (
      if p.val < 15 then (
        if p.val < 7 then (
          if p.val < 3 then (
            if p.val < 1 then (
              15
            ) else (
              if p.val < 2 then (
                7
              ) else (
                15
              )
            )
          ) else (
            if p.val < 5 then (
              if p.val < 4 then (
                11
              ) else (
                3
              )
            ) else (
              if p.val < 6 then (
                3
              ) else (
                15
              )
            )
          )
        ) else (
          if p.val < 11 then (
            if p.val < 9 then (
              if p.val < 8 then (
                7
              ) else (
                15
              )
            ) else (
              if p.val < 10 then (
                13
              ) else (
                5
              )
            )
          ) else (
            if p.val < 13 then (
              if p.val < 12 then (
                5
              ) else (
                15
              )
            ) else (
              if p.val < 14 then (
                11
              ) else (
                15
              )
            )
          )
        )
      ) else (
        if p.val < 22 then (
          if p.val < 18 then (
            if p.val < 16 then (
              13
            ) else (
              if p.val < 17 then (
                9
              ) else (
                9
              )
            )
          ) else (
            if p.val < 20 then (
              if p.val < 19 then (
                1
              ) else (
                1
              )
            ) else (
              if p.val < 21 then (
                1
              ) else (
                1
              )
            )
          )
        ) else (
          if p.val < 26 then (
            if p.val < 24 then (
              if p.val < 23 then (
                1
              ) else (
                1
              )
            ) else (
              if p.val < 25 then (
                15
              ) else (
                7
              )
            )
          ) else (
            if p.val < 28 then (
              if p.val < 27 then (
                15
              ) else (
                11
              )
            ) else (
              if p.val < 29 then (
                3
              ) else (
                3
              )
            )
          )
        )
      )
    ) else (
      if p.val < 45 then (
        if p.val < 37 then (
          if p.val < 33 then (
            if p.val < 31 then (
              15
            ) else (
              if p.val < 32 then (
                7
              ) else (
                15
              )
            )
          ) else (
            if p.val < 35 then (
              if p.val < 34 then (
                14
              ) else (
                6
              )
            ) else (
              if p.val < 36 then (
                6
              ) else (
                15
              )
            )
          )
        ) else (
          if p.val < 41 then (
            if p.val < 39 then (
              if p.val < 38 then (
                11
              ) else (
                15
              )
            ) else (
              if p.val < 40 then (
                14
              ) else (
                10
              )
            )
          ) else (
            if p.val < 43 then (
              if p.val < 42 then (
                10
              ) else (
                2
              )
            ) else (
              if p.val < 44 then (
                2
              ) else (
                2
              )
            )
          )
        )
      ) else (
        if p.val < 52 then (
          if p.val < 48 then (
            if p.val < 46 then (
              2
            ) else (
              if p.val < 47 then (
                2
              ) else (
                2
              )
            )
          ) else (
            if p.val < 50 then (
              if p.val < 49 then (
                15
              ) else (
                7
              )
            ) else (
              if p.val < 51 then (
                15
              ) else (
                13
              )
            )
          )
        ) else (
          if p.val < 56 then (
            if p.val < 54 then (
              if p.val < 53 then (
                5
              ) else (
                5
              )
            ) else (
              if p.val < 55 then (
                15
              ) else (
                7
              )
            )
          ) else (
            if p.val < 58 then (
              if p.val < 57 then (
                15
              ) else (
                14
              )
            ) else (
              if p.val < 59 then (
                6
              ) else (
                6
              )
            )
          )
        )
      )
    )
  ) else (
    if p.val < 90 then (
      if p.val < 75 then (
        if p.val < 67 then (
          if p.val < 63 then (
            if p.val < 61 then (
              15
            ) else (
              if p.val < 62 then (
                13
              ) else (
                15
              )
            )
          ) else (
            if p.val < 65 then (
              if p.val < 64 then (
                14
              ) else (
                12
              )
            ) else (
              if p.val < 66 then (
                12
              ) else (
                4
              )
            )
          )
        ) else (
          if p.val < 71 then (
            if p.val < 69 then (
              if p.val < 68 then (
                4
              ) else (
                4
              )
            ) else (
              if p.val < 70 then (
                4
              ) else (
                4
              )
            )
          ) else (
            if p.val < 73 then (
              if p.val < 72 then (
                4
              ) else (
                15
              )
            ) else (
              if p.val < 74 then (
                11
              ) else (
                15
              )
            )
          )
        )
      ) else (
        if p.val < 82 then (
          if p.val < 78 then (
            if p.val < 76 then (
              13
            ) else (
              if p.val < 77 then (
                9
              ) else (
                9
              )
            )
          ) else (
            if p.val < 80 then (
              if p.val < 79 then (
                15
              ) else (
                11
              )
            ) else (
              if p.val < 81 then (
                15
              ) else (
                14
              )
            )
          )
        ) else (
          if p.val < 86 then (
            if p.val < 84 then (
              if p.val < 83 then (
                10
              ) else (
                10
              )
            ) else (
              if p.val < 85 then (
                15
              ) else (
                13
              )
            )
          ) else (
            if p.val < 88 then (
              if p.val < 87 then (
                15
              ) else (
                14
              )
            ) else (
              if p.val < 89 then (
                12
              ) else (
                12
              )
            )
          )
        )
      )
    ) else (
      if p.val < 105 then (
        if p.val < 97 then (
          if p.val < 93 then (
            if p.val < 91 then (
              8
            ) else (
              if p.val < 92 then (
                8
              ) else (
                8
              )
            )
          ) else (
            if p.val < 95 then (
              if p.val < 94 then (
                8
              ) else (
                8
              )
            ) else (
              if p.val < 96 then (
                8
              ) else (
                0
              )
            )
          )
        ) else (
          if p.val < 101 then (
            if p.val < 99 then (
              if p.val < 98 then (
                0
              ) else (
                0
              )
            ) else (
              if p.val < 100 then (
                0
              ) else (
                0
              )
            )
          ) else (
            if p.val < 103 then (
              if p.val < 102 then (
                0
              ) else (
                0
              )
            ) else (
              if p.val < 104 then (
                0
              ) else (
                0
              )
            )
          )
        )
      ) else (
        if p.val < 112 then (
          if p.val < 108 then (
            if p.val < 106 then (
              0
            ) else (
              if p.val < 107 then (
                0
              ) else (
                0
              )
            )
          ) else (
            if p.val < 110 then (
              if p.val < 109 then (
                0
              ) else (
                0
              )
            ) else (
              if p.val < 111 then (
                0
              ) else (
                0
              )
            )
          )
        ) else (
          if p.val < 116 then (
            if p.val < 114 then (
              if p.val < 113 then (
                0
              ) else (
                0
              )
            ) else (
              if p.val < 115 then (
                0
              ) else (
                0
              )
            )
          ) else (
            if p.val < 118 then (
              if p.val < 117 then (
                0
              ) else (
                0
              )
            ) else (
              if p.val < 119 then (
                0
              ) else (
                0
              )
            )
          )
        )
      )
    )
  )

theorem fastCenterBeforeMask_eq : ∀ p : Fin 120, fastCenterBeforeMask p = centerBeforeMask p := by decide

def fastMaskedChain (T : Fin 16) (p : Fin 120) (j : Fin 4) : FormRef 15 :=
  maskRef (fastChainNegative p j) (Nat.land T.val (fastChainMask p j))

def fastMaskedCoarse (T : Fin 16) (p : Fin 120) (j : Fin 10) : FormRef 15 :=
  maskRef (fastCoarseNegative p j) (Nat.land T.val (fastCoarseMask p j))

theorem fastMaskedChain_eq (T : Fin 16) (p : Fin 120) (j : Fin 4) :
    fastMaskedChain T p j = maskedChain T p j := by
  simp only [fastMaskedChain, maskedChain, fastChainNegative_eq, fastChainMask_eq]

theorem fastMaskedCoarse_eq (T : Fin 16) (p : Fin 120) (j : Fin 10) :
    fastMaskedCoarse T p j = maskedCoarse T p j := by
  simp only [fastMaskedCoarse, maskedCoarse, fastCoarseNegative_eq, fastCoarseMask_eq]

end MaxCaterpillar.Frontier.StarCertificate
