import MaxCaterpillar.Frontier.StarCertificate.XiSelectors
/-! Generated integral coefficient data; equality with the rational dictionary
is proved below, so this is an arithmetic representation of the same Xi. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators
abbrev IntegerForm (n : ℕ) := Fin n → ℤ

def starIntegerKappa (p : Fin 10 → Sign) : IntegerForm 4 :=
  let code := coarsePatternCode p
  if code < 32969 then (
    if code < 13184 then (
      if code < 4556 then (
        if code < 668 then (
          if code < 227 then (
            if code < 191 then (
              if code < 173 then (
                if code = 164 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 182 then (
                  if code = 173 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
                ) else (
                  if code = 182 then ![(0 : ℤ), (2 : ℤ), (-2 : ℤ), (-2 : ℤ)] else 0
                )
              )
            ) else (
              if code < 209 then (
                if code < 200 then (
                  if code = 191 then ![(0 : ℤ), (16 : ℤ), (-18 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 200 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 218 then (
                  if code = 209 then ![(0 : ℤ), (28 : ℤ), (-28 : ℤ), (-4 : ℤ)] else 0
                ) else (
                  if code = 218 then ![(0 : ℤ), (2 : ℤ), (-3 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 416 then (
              if code < 236 then (
                if code = 227 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
              ) else (
                if code < 407 then (
                  if code = 236 then ![(0 : ℤ), (2 : ℤ), (-2 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 407 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (24 : ℤ)] else 0
                )
              )
            ) else (
              if code < 650 then (
                if code < 425 then (
                  if code = 416 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 425 then ![(-2 : ℤ), (2 : ℤ), (0 : ℤ), (22 : ℤ)] else 0
                )
              ) else (
                if code < 659 then (
                  if code = 650 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 659 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 2603 then (
            if code < 2369 then (
              if code < 2351 then (
                if code = 668 then ![(0 : ℤ), (2 : ℤ), (-2 : ℤ), (-2 : ℤ)] else 0
              ) else (
                if code < 2360 then (
                  if code = 2351 then ![(0 : ℤ), (-18 : ℤ), (16 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 2360 then ![(48 : ℤ), (0 : ℤ), (48 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 2423 then (
                if code < 2396 then (
                  if code = 2369 then ![(0 : ℤ), (-20 : ℤ), (22 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 2396 then ![(-2 : ℤ), (0 : ℤ), (0 : ℤ), (26 : ℤ)] else 0
                )
              ) else (
                if code < 2594 then (
                  if code = 2423 then ![(2 : ℤ), (0 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 2594 then ![(-2 : ℤ), (0 : ℤ), (0 : ℤ), (6 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 2846 then (
              if code < 2612 then (
                if code = 2603 then ![(72 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 2837 then (
                  if code = 2612 then ![(0 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 2837 then ![(0 : ℤ), (-18 : ℤ), (16 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 4538 then (
                if code < 2855 then (
                  if code = 2846 then ![(48 : ℤ), (0 : ℤ), (48 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 2855 then ![(0 : ℤ), (-20 : ℤ), (22 : ℤ), (-2 : ℤ)] else 0
                )
              ) else (
                if code < 4547 then (
                  if code = 4538 then ![(2 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 4547 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
                )
              )
            )
          )
        )
      ) else (
        if code < 5528 then (
          if code < 5032 then (
            if code < 4781 then (
              if code < 4583 then (
                if code = 4556 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (-6 : ℤ)] else 0
              ) else (
                if code < 4610 then (
                  if code = 4583 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (18 : ℤ)] else 0
                ) else (
                  if code = 4610 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (-6 : ℤ)] else 0
                )
              )
            ) else (
              if code < 4799 then (
                if code < 4790 then (
                  if code = 4781 then ![(2 : ℤ), (-1 : ℤ), (0 : ℤ), (24 : ℤ)] else 0
                ) else (
                  if code = 4790 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 5024 then (
                  if code = 4799 then ![(6 : ℤ), (-2 : ℤ), (0 : ℤ), (18 : ℤ)] else 0
                ) else (
                  if code = 5024 then ![(2 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 5042 then (
              if code < 5033 then (
                if code = 5032 then ![(0 : ℤ), (0 : ℤ), (-6 : ℤ), (-14 : ℤ)] else 0
              ) else (
                if code < 5041 then (
                  if code = 5033 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
                ) else (
                  if code = 5041 then ![(0 : ℤ), (10 : ℤ), (-6 : ℤ), (-2 : ℤ)] else 0
                )
              )
            ) else (
              if code < 5312 then (
                if code < 5285 then (
                  if code = 5042 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 5285 then ![(-2 : ℤ), (0 : ℤ), (4 : ℤ), (-52 : ℤ)] else 0
                )
              ) else (
                if code < 5339 then (
                  if code = 5312 then ![(0 : ℤ), (1 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
                ) else (
                  if code = 5339 then ![(-2 : ℤ), (0 : ℤ), (4 : ℤ), (-52 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 6499 then (
            if code < 6014 then (
              if code < 5770 then (
                if code = 5528 then ![(0 : ℤ), (1 : ℤ), (0 : ℤ), (-27 : ℤ)] else 0
              ) else (
                if code < 5771 then (
                  if code = 5770 then ![(0 : ℤ), (4 : ℤ), (0 : ℤ), (-56 : ℤ)] else 0
                ) else (
                  if code = 5771 then ![(-2 : ℤ), (0 : ℤ), (4 : ℤ), (-52 : ℤ)] else 0
                )
              )
            ) else (
              if code < 6068 then (
                if code < 6041 then (
                  if code = 6014 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 6041 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (18 : ℤ)] else 0
                )
              ) else (
                if code < 6257 then (
                  if code = 6068 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 6257 then ![(6 : ℤ), (-2 : ℤ), (0 : ℤ), (18 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 6752 then (
              if code < 6500 then (
                if code = 6499 then ![(0 : ℤ), (10 : ℤ), (-6 : ℤ), (-2 : ℤ)] else 0
              ) else (
                if code < 6725 then (
                  if code = 6500 then ![(0 : ℤ), (-2 : ℤ), (6 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 6725 then ![(24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 6968 then (
                if code < 6779 then (
                  if code = 6752 then ![(6 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 6779 then ![(24 : ℤ), (2 : ℤ), (-1 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 7211 then (
                  if code = 6968 then ![(24 : ℤ), (24 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 7211 then ![(24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          )
        )
      )
    ) else (
      if code < 15128 then (
        if code < 13670 then (
          if code < 13427 then (
            if code < 13313 then (
              if code < 13265 then (
                if code = 13184 then ![(10 : ℤ), (-18 : ℤ), (14 : ℤ), (-4 : ℤ)] else 0
              ) else (
                if code < 13286 then (
                  if code = 13265 then ![(10 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13286 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 13343 then (
                if code < 13340 then (
                  if code = 13313 then ![(0 : ℤ), (16 : ℤ), (-18 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13340 then ![(0 : ℤ), (0 : ℤ), (-1 : ℤ), (2 : ℤ)] else 0
                )
              ) else (
                if code < 13346 then (
                  if code = 13343 then ![(10 : ℤ), (-18 : ℤ), (13 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13346 then ![(10 : ℤ), (-14 : ℤ), (5 : ℤ), (2 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 13559 then (
              if code < 13508 then (
                if code = 13427 then ![(24 : ℤ), (-18 : ℤ), (0 : ℤ), (-4 : ℤ)] else 0
              ) else (
                if code < 13529 then (
                  if code = 13508 then ![(10 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13529 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (24 : ℤ)] else 0
                )
              )
            ) else (
              if code < 13616 then (
                if code < 13589 then (
                  if code = 13559 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13589 then ![(15 : ℤ), (-14 : ℤ), (0 : ℤ), (2 : ℤ)] else 0
                )
              ) else (
                if code < 13643 then (
                  if code = 13616 then ![(10 : ℤ), (-18 : ℤ), (14 : ℤ), (-4 : ℤ)] else 0
                ) else (
                  if code = 13643 then ![(0 : ℤ), (2 : ℤ), (-4 : ℤ), (-14 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 13805 then (
            if code < 13751 then (
              if code < 13697 then (
                if code = 13670 then ![(10 : ℤ), (-18 : ℤ), (14 : ℤ), (-4 : ℤ)] else 0
              ) else (
                if code < 13724 then (
                  if code = 13697 then ![(10 : ℤ), (-12 : ℤ), (10 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13724 then ![(0 : ℤ), (8 : ℤ), (-13 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 13775 then (
                if code < 13772 then (
                  if code = 13751 then ![(10 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13772 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 13778 then (
                  if code = 13775 then ![(10 : ℤ), (-18 : ℤ), (14 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 13778 then ![(10 : ℤ), (-14 : ℤ), (6 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 14156 then (
              if code < 13832 then (
                if code = 13805 then ![(0 : ℤ), (0 : ℤ), (-2 : ℤ), (-10 : ℤ)] else 0
              ) else (
                if code < 13913 then (
                  if code = 13832 then ![(10 : ℤ), (-14 : ℤ), (5 : ℤ), (2 : ℤ)] else 0
                ) else (
                  if code = 13913 then ![(0 : ℤ), (-14 : ℤ), (12 : ℤ), (30 : ℤ)] else 0
                )
              )
            ) else (
              if code < 14642 then (
                if code < 14399 then (
                  if code = 14156 then ![(0 : ℤ), (-8 : ℤ), (0 : ℤ), (36 : ℤ)] else 0
                ) else (
                  if code = 14399 then ![(0 : ℤ), (-14 : ℤ), (12 : ℤ), (30 : ℤ)] else 0
                )
              ) else (
                if code < 14885 then (
                  if code = 14642 then ![(8 : ℤ), (-17 : ℤ), (14 : ℤ), (-4 : ℤ)] else 0
                ) else (
                  if code = 14885 then ![(22 : ℤ), (-17 : ℤ), (0 : ℤ), (-4 : ℤ)] else 0
                )
              )
            )
          )
        )
      ) else (
        if code < 24481 then (
          if code < 22070 then (
            if code < 19901 then (
              if code < 19847 then (
                if code = 15128 then ![(8 : ℤ), (-17 : ℤ), (14 : ℤ), (-4 : ℤ)] else 0
              ) else (
                if code < 19874 then (
                  if code = 19847 then ![(-24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 19874 then ![(0 : ℤ), (48 : ℤ), (0 : ℤ), (48 : ℤ)] else 0
                )
              )
            ) else (
              if code < 19919 then (
                if code < 19910 then (
                  if code = 19901 then ![(-24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 19910 then ![(-18 : ℤ), (0 : ℤ), (0 : ℤ), (-18 : ℤ)] else 0
                )
              ) else (
                if code < 22034 then (
                  if code = 19919 then ![(6 : ℤ), (-4 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 22034 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 24230 then (
              if code < 22106 then (
                if code = 22070 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 24221 then (
                  if code = 22106 then ![(2 : ℤ), (0 : ℤ), (0 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 24221 then ![(-24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 24266 then (
                if code < 24239 then (
                  if code = 24230 then ![(-18 : ℤ), (0 : ℤ), (0 : ℤ), (-18 : ℤ)] else 0
                ) else (
                  if code = 24239 then ![(6 : ℤ), (-8 : ℤ), (0 : ℤ), (-6 : ℤ)] else 0
                )
              ) else (
                if code < 24293 then (
                  if code = 24266 then ![(0 : ℤ), (-8 : ℤ), (0 : ℤ), (12 : ℤ)] else 0
                ) else (
                  if code = 24293 then ![(6 : ℤ), (-8 : ℤ), (0 : ℤ), (-6 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 25751 then (
            if code < 25022 then (
              if code < 24968 then (
                if code = 24481 then ![(0 : ℤ), (4 : ℤ), (0 : ℤ), (22 : ℤ)] else 0
              ) else (
                if code < 24995 then (
                  if code = 24968 then ![(-2 : ℤ), (0 : ℤ), (0 : ℤ), (-46 : ℤ)] else 0
                ) else (
                  if code = 24995 then ![(0 : ℤ), (10 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 25697 then (
                if code < 25210 then (
                  if code = 25022 then ![(-2 : ℤ), (0 : ℤ), (0 : ℤ), (-46 : ℤ)] else 0
                ) else (
                  if code = 25210 then ![(0 : ℤ), (30 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 25724 then (
                  if code = 25697 then ![(6 : ℤ), (-8 : ℤ), (0 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 25724 then ![(0 : ℤ), (-8 : ℤ), (0 : ℤ), (12 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 26435 then (
              if code < 25939 then (
                if code = 25751 then ![(6 : ℤ), (-8 : ℤ), (0 : ℤ), (-6 : ℤ)] else 0
              ) else (
                if code < 26408 then (
                  if code = 25939 then ![(0 : ℤ), (4 : ℤ), (0 : ℤ), (22 : ℤ)] else 0
                ) else (
                  if code = 26408 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 32867 then (
                if code < 26462 then (
                  if code = 26435 then ![(0 : ℤ), (72 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 26462 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 32948 then (
                  if code = 32867 then ![(-8 : ℤ), (0 : ℤ), (0 : ℤ), (-4 : ℤ)] else 0
                ) else (
                  if code = 32948 then ![(16 : ℤ), (-20 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          )
        )
      )
    )
  ) else (
    if code < 44705 then (
      if code < 41771 then (
        if code < 40313 then (
          if code < 39530 then (
            if code < 33026 then (
              if code < 32996 then (
                if code = 32969 then ![(-24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 33023 then (
                  if code = 32996 then ![(0 : ℤ), (48 : ℤ), (0 : ℤ), (48 : ℤ)] else 0
                ) else (
                  if code = 33023 then ![(-24 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 33596 then (
                if code < 33029 then (
                  if code = 33026 then ![(-14 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 33029 then ![(-8 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 34325 then (
                  if code = 33596 then ![(-12 : ℤ), (-44 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 34325 then ![(-8 : ℤ), (0 : ℤ), (0 : ℤ), (-4 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 39593 then (
              if code < 39557 then (
                if code = 39530 then ![(-2 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 39584 then (
                  if code = 39557 then ![(-2 : ℤ), (22 : ℤ), (-20 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 39584 then ![(-6 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 39605 then (
                if code < 39602 then (
                  if code = 39593 then ![(-6 : ℤ), (0 : ℤ), (-8 : ℤ), (6 : ℤ)] else 0
                ) else (
                  if code = 39602 then ![(-6 : ℤ), (8 : ℤ), (-5 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 39608 then (
                  if code = 39605 then ![(-2 : ℤ), (-8 : ℤ), (15 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 39608 then ![(4 : ℤ), (-14 : ℤ), (17 : ℤ), (-8 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 41042 then (
            if code < 40334 then (
              if code < 40322 then (
                if code = 40313 then ![(-52 : ℤ), (4 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
              ) else (
                if code < 40331 then (
                  if code = 40322 then ![(-46 : ℤ), (0 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 40331 then ![(-32 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ)] else 0
                )
              )
            ) else (
              if code < 40904 then (
                if code < 40337 then (
                  if code = 40334 then ![(-40 : ℤ), (0 : ℤ), (2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 40337 then ![(-30 : ℤ), (-12 : ℤ), (14 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 40985 then (
                  if code = 40904 then ![(-2 : ℤ), (-5 : ℤ), (14 : ℤ), (-10 : ℤ)] else 0
                ) else (
                  if code = 40985 then ![(-10 : ℤ), (0 : ℤ), (6 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 41063 then (
              if code < 41051 then (
                if code = 41042 then ![(-6 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 41060 then (
                  if code = 41051 then ![(-6 : ℤ), (0 : ℤ), (-8 : ℤ), (6 : ℤ)] else 0
                ) else (
                  if code = 41060 then ![(-6 : ℤ), (8 : ℤ), (-4 : ℤ), (-2 : ℤ)] else 0
                )
              )
            ) else (
              if code < 41717 then (
                if code < 41066 then (
                  if code = 41063 then ![(-2 : ℤ), (-8 : ℤ), (16 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 41066 then ![(4 : ℤ), (-14 : ℤ), (18 : ℤ), (-10 : ℤ)] else 0
                )
              ) else (
                if code < 41744 then (
                  if code = 41717 then ![(-4 : ℤ), (-28 : ℤ), (28 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 41744 then ![(26 : ℤ), (0 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
                )
              )
            )
          )
        )
      ) else (
        if code < 43913 then (
          if code < 43172 then (
            if code < 42500 then (
              if code < 41780 then (
                if code = 41771 then ![(18 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 41789 then (
                  if code = 41780 then ![(12 : ℤ), (0 : ℤ), (-8 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 41789 then ![(20 : ℤ), (14 : ℤ), (-10 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 42518 then (
                if code < 42509 then (
                  if code = 42500 then ![(-24 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 42509 then ![(0 : ℤ), (0 : ℤ), (10 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 43091 then (
                  if code = 42518 then ![(0 : ℤ), (0 : ℤ), (-14 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 43091 then ![(10 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 43247 then (
              if code < 43229 then (
                if code = 43172 then ![(0 : ℤ), (13 : ℤ), (-8 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 43238 then (
                  if code = 43229 then ![(18 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 43238 then ![(12 : ℤ), (0 : ℤ), (-8 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 43253 then (
                if code < 43250 then (
                  if code = 43247 then ![(20 : ℤ), (8 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 43250 then ![(18 : ℤ), (0 : ℤ), (-4 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 43904 then (
                  if code = 43253 then ![(14 : ℤ), (4 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 43904 then ![(-2 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 43967 then (
            if code < 43931 then (
              if code < 43921 then (
                if code = 43913 then ![(-2 : ℤ), (0 : ℤ), (-4 : ℤ), (6 : ℤ)] else 0
              ) else (
                if code < 43922 then (
                  if code = 43921 then ![(0 : ℤ), (15 : ℤ), (-8 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 43922 then ![(0 : ℤ), (-5 : ℤ), (8 : ℤ), (-6 : ℤ)] else 0
                )
              )
            ) else (
              if code < 43949 then (
                if code < 43940 then (
                  if code = 43931 then ![(0 : ℤ), (-2 : ℤ), (0 : ℤ), (2 : ℤ)] else 0
                ) else (
                  if code = 43940 then ![(-6 : ℤ), (0 : ℤ), (0 : ℤ), (2 : ℤ)] else 0
                )
              ) else (
                if code < 43958 then (
                  if code = 43949 then ![(0 : ℤ), (-10 : ℤ), (14 : ℤ), (20 : ℤ)] else 0
                ) else (
                  if code = 43958 then ![(-6 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 44651 then (
              if code < 43976 then (
                if code = 43967 then ![(-6 : ℤ), (0 : ℤ), (-8 : ℤ), (6 : ℤ)] else 0
              ) else (
                if code < 44650 then (
                  if code = 43976 then ![(-6 : ℤ), (4 : ℤ), (4 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 44650 then ![(0 : ℤ), (2 : ℤ), (0 : ℤ), (-40 : ℤ)] else 0
                )
              )
            ) else (
              if code < 44687 then (
                if code < 44678 then (
                  if code = 44651 then ![(-24 : ℤ), (0 : ℤ), (0 : ℤ), (-32 : ℤ)] else 0
                ) else (
                  if code = 44678 then ![(0 : ℤ), (-14 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 44696 then (
                  if code = 44687 then ![(-52 : ℤ), (4 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 44696 then ![(-46 : ℤ), (0 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
                )
              )
            )
          )
        )
      )
    ) else (
      if code < 49651 then (
        if code < 45440 then (
          if code < 45406 then (
            if code < 45355 then (
              if code < 45277 then (
                if code = 44705 then ![(-30 : ℤ), (0 : ℤ), (0 : ℤ), (-30 : ℤ)] else 0
              ) else (
                if code < 45278 then (
                  if code = 45277 then ![(0 : ℤ), (-14 : ℤ), (18 : ℤ), (-10 : ℤ)] else 0
                ) else (
                  if code = 45278 then ![(0 : ℤ), (-6 : ℤ), (14 : ℤ), (-10 : ℤ)] else 0
                )
              )
            ) else (
              if code < 45379 then (
                if code < 45359 then (
                  if code = 45355 then ![(0 : ℤ), (12 : ℤ), (12 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 45359 then ![(-10 : ℤ), (-10 : ℤ), (12 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 45380 then (
                  if code = 45379 then ![(0 : ℤ), (16 : ℤ), (-8 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 45380 then ![(-2 : ℤ), (-4 : ℤ), (8 : ℤ), (-6 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 45425 then (
              if code < 45407 then (
                if code = 45406 then ![(0 : ℤ), (-4 : ℤ), (18 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 45416 then (
                  if code = 45407 then ![(0 : ℤ), (0 : ℤ), (8 : ℤ), (20 : ℤ)] else 0
                ) else (
                  if code = 45416 then ![(-6 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 45434 then (
                if code < 45433 then (
                  if code = 45425 then ![(-6 : ℤ), (0 : ℤ), (-8 : ℤ), (6 : ℤ)] else 0
                ) else (
                  if code = 45433 then ![(0 : ℤ), (16 : ℤ), (-8 : ℤ), (-2 : ℤ)] else 0
                )
              ) else (
                if code < 45437 then (
                  if code = 45434 then ![(-6 : ℤ), (4 : ℤ), (4 : ℤ), (-6 : ℤ)] else 0
                ) else (
                  if code = 45437 then ![(-2 : ℤ), (-8 : ℤ), (16 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 46886 then (
            if code < 46145 then (
              if code < 46091 then (
                if code = 45440 then ![(4 : ℤ), (-14 : ℤ), (18 : ℤ), (-10 : ℤ)] else 0
              ) else (
                if code < 46118 then (
                  if code = 46091 then ![(22 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 46118 then ![(0 : ℤ), (0 : ℤ), (2 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 46169 then (
                if code < 46157 then (
                  if code = 46145 then ![(18 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 46157 then ![(22 : ℤ), (0 : ℤ), (4 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 46874 then (
                  if code = 46169 then ![(4 : ℤ), (-22 : ℤ), (17 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 46874 then ![(-27 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 47546 then (
              if code < 46898 then (
                if code = 46886 then ![(0 : ℤ), (0 : ℤ), (30 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 47465 then (
                  if code = 46898 then ![(-36 : ℤ), (0 : ℤ), (8 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 47465 then ![(-2 : ℤ), (-15 : ℤ), (14 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 47615 then (
                if code < 47603 then (
                  if code = 47546 then ![(-10 : ℤ), (0 : ℤ), (6 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 47603 then ![(18 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 47627 then (
                  if code = 47615 then ![(22 : ℤ), (0 : ℤ), (4 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 47627 then ![(4 : ℤ), (-24 : ℤ), (18 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          )
        )
      ) else (
        if code < 53441 then (
          if code < 52712 then (
            if code < 52652 then (
              if code < 52550 then (
                if code = 49651 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 52631 then (
                  if code = 52550 then ![(0 : ℤ), (-4 : ℤ), (8 : ℤ), (-4 : ℤ)] else 0
                ) else (
                  if code = 52631 then ![(0 : ℤ), (0 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 52706 then (
                if code < 52679 then (
                  if code = 52652 then ![(-2 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 52679 then ![(-2 : ℤ), (22 : ℤ), (-20 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 52709 then (
                  if code = 52706 then ![(-6 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 52709 then ![(-2 : ℤ), (-6 : ℤ), (10 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 53279 then (
              if code < 52721 then (
                if code = 52712 then ![(4 : ℤ), (-8 : ℤ), (4 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 52730 then (
                  if code = 52721 then ![(4 : ℤ), (0 : ℤ), (0 : ℤ), (8 : ℤ)] else 0
                ) else (
                  if code = 52730 then ![(4 : ℤ), (-12 : ℤ), (15 : ℤ), (-10 : ℤ)] else 0
                )
              )
            ) else (
              if code < 53435 then (
                if code < 53360 then (
                  if code = 53279 then ![(0 : ℤ), (0 : ℤ), (4 : ℤ), (22 : ℤ)] else 0
                ) else (
                  if code = 53360 then ![(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 53438 then (
                  if code = 53435 then ![(-52 : ℤ), (4 : ℤ), (0 : ℤ), (-2 : ℤ)] else 0
                ) else (
                  if code = 53438 then ![(-56 : ℤ), (0 : ℤ), (4 : ℤ), (0 : ℤ)] else 0
                )
              )
            )
          )
        ) else (
          if code < 54089 then (
            if code < 54008 then (
              if code < 53450 then (
                if code = 53441 then ![(-22 : ℤ), (-4 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
              ) else (
                if code < 53459 then (
                  if code = 53450 then ![(0 : ℤ), (0 : ℤ), (44 : ℤ), (12 : ℤ)] else 0
                ) else (
                  if code = 53459 then ![(-30 : ℤ), (-12 : ℤ), (14 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 54025 then (
                if code < 54017 then (
                  if code = 54008 then ![(0 : ℤ), (-4 : ℤ), (8 : ℤ), (-4 : ℤ)] else 0
                ) else (
                  if code = 54017 then ![(0 : ℤ), (0 : ℤ), (-4 : ℤ), (8 : ℤ)] else 0
                )
              ) else (
                if code < 54026 then (
                  if code = 54025 then ![(0 : ℤ), (-13 : ℤ), (18 : ℤ), (-10 : ℤ)] else 0
                ) else (
                  if code = 54026 then ![(-2 : ℤ), (-5 : ℤ), (14 : ℤ), (-10 : ℤ)] else 0
                )
              )
            )
          ) else (
            if code < 54167 then (
              if code < 54107 then (
                if code < 54098 then (
                  if code = 54089 then ![(0 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 54098 then ![(-16 : ℤ), (0 : ℤ), (20 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 54164 then (
                  if code = 54107 then ![(-10 : ℤ), (0 : ℤ), (6 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 54164 then ![(-6 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ)] else 0
                )
              )
            ) else (
              if code < 54179 then (
                if code < 54170 then (
                  if code = 54167 then ![(-2 : ℤ), (-6 : ℤ), (10 : ℤ), (0 : ℤ)] else 0
                ) else (
                  if code = 54170 then ![(4 : ℤ), (-8 : ℤ), (4 : ℤ), (0 : ℤ)] else 0
                )
              ) else (
                if code < 54188 then (
                  if code = 54179 then ![(4 : ℤ), (0 : ℤ), (0 : ℤ), (8 : ℤ)] else 0
                ) else (
                  if code = 54188 then ![(4 : ℤ), (-14 : ℤ), (18 : ℤ), (-10 : ℤ)] else 0
                )
              )
            )
          )
        )
      )
    )
  )

theorem starIntegerKappa_cast (p : Fin 10 → Sign) :
    (fun j => (starIntegerKappa p j : ℚ)) = starKappa p := by
  funext j
  fin_cases j <;> norm_num [starIntegerKappa, starKappa, ite_apply, Int.cast_ite]

end MaxCaterpillar.Frontier.StarCertificate
