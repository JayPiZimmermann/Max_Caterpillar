import research.sN.width_tradeoff.UpperNineCells0
import research.sN.width_tradeoff.UpperNineCells1
import research.sN.width_tradeoff.UpperNineCells2
import research.sN.width_tradeoff.UpperNineCells3
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.WidthTradeoff.P4
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections

theorem identity (x : Point 5) : Maximum 5 x = rhs x := by
  rcases le_total (x 1) (x 0) with h0 | h0
  ·
    rcases le_total (x 2) (x 0) with h1 | h1
    ·
      rcases le_total (x 2) (x 1) with h2 | h2
      ·
        rcases le_total (x 3) (x 0) with h3 | h3
        ·
          rcases le_total (x 3) (x 1) with h4 | h4
          ·
            rcases le_total (x 3) (x 2) with h5 | h5
            ·
              rcases le_total (x 4) (x 0) with h6 | h6
              ·
                rcases le_total (x 4) (x 1) with h7 | h7
                ·
                  rcases le_total (x 4) (x 2) with h8 | h8
                  ·
                    rcases le_total (x 4) (x 3) with h9 | h9
                    ·
                      exact chamber0 x (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9])
                    ·
                      exact chamber1 x (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9])
                  ·
                    exact chamber4 x (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8])
                ·
                  exact chamber18 x (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7]) (by linarith only [h0,h1,h2,h3,h4,h5,h6,h7])
              ·
                exact chamber96 x (by linarith only [h0,h1,h2,h3,h4,h5,h6]) (by linarith only [h0,h1,h2,h3,h4,h5,h6]) (by linarith only [h0,h1,h2,h3,h4,h5,h6]) (by linarith only [h0,h1,h2,h3,h4,h5,h6])
            ·
              rcases le_total (x 4) (x 0) with h10 | h10
              ·
                rcases le_total (x 4) (x 1) with h11 | h11
                ·
                  rcases le_total (x 4) (x 3) with h12 | h12
                  ·
                    rcases le_total (x 4) (x 2) with h13 | h13
                    ·
                      exact chamber2 x (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13])
                    ·
                      exact chamber3 x (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12,h13])
                  ·
                    exact chamber5 x (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11,h12])
                ·
                  exact chamber19 x (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11]) (by linarith only [h0,h1,h2,h3,h4,h5,h10,h11])
              ·
                exact chamber97 x (by linarith only [h0,h1,h2,h3,h4,h5,h10]) (by linarith only [h0,h1,h2,h3,h4,h5,h10]) (by linarith only [h0,h1,h2,h3,h4,h5,h10]) (by linarith only [h0,h1,h2,h3,h4,h5,h10])
          ·
            rcases le_total (x 4) (x 0) with h14 | h14
            ·
              rcases le_total (x 4) (x 3) with h15 | h15
              ·
                rcases le_total (x 4) (x 1) with h16 | h16
                ·
                  rcases le_total (x 4) (x 2) with h17 | h17
                  ·
                    exact chamber12 x (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17])
                  ·
                    exact chamber13 x (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16,h17])
                ·
                  exact chamber16 x (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16]) (by linarith only [h0,h1,h2,h3,h4,h14,h15,h16])
              ·
                exact chamber22 x (by linarith only [h0,h1,h2,h3,h4,h14,h15]) (by linarith only [h0,h1,h2,h3,h4,h14,h15]) (by linarith only [h0,h1,h2,h3,h4,h14,h15]) (by linarith only [h0,h1,h2,h3,h4,h14,h15])
            ·
              exact chamber100 x (by linarith only [h0,h1,h2,h3,h4,h14]) (by linarith only [h0,h1,h2,h3,h4,h14]) (by linarith only [h0,h1,h2,h3,h4,h14]) (by linarith only [h0,h1,h2,h3,h4,h14])
        ·
          rcases le_total (x 4) (x 3) with h18 | h18
          ·
            rcases le_total (x 4) (x 0) with h19 | h19
            ·
              rcases le_total (x 4) (x 1) with h20 | h20
              ·
                rcases le_total (x 4) (x 2) with h21 | h21
                ·
                  exact chamber72 x (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21]) (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21]) (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21]) (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21])
                ·
                  exact chamber73 x (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21]) (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21]) (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21]) (by linarith only [h0,h1,h2,h3,h18,h19,h20,h21])
              ·
                exact chamber76 x (by linarith only [h0,h1,h2,h3,h18,h19,h20]) (by linarith only [h0,h1,h2,h3,h18,h19,h20]) (by linarith only [h0,h1,h2,h3,h18,h19,h20]) (by linarith only [h0,h1,h2,h3,h18,h19,h20])
            ·
              exact chamber90 x (by linarith only [h0,h1,h2,h3,h18,h19]) (by linarith only [h0,h1,h2,h3,h18,h19]) (by linarith only [h0,h1,h2,h3,h18,h19]) (by linarith only [h0,h1,h2,h3,h18,h19])
          ·
            exact chamber114 x (by linarith only [h0,h1,h2,h3,h18]) (by linarith only [h0,h1,h2,h3,h18]) (by linarith only [h0,h1,h2,h3,h18]) (by linarith only [h0,h1,h2,h3,h18])
      ·
        rcases le_total (x 3) (x 0) with h22 | h22
        ·
          rcases le_total (x 3) (x 2) with h23 | h23
          ·
            rcases le_total (x 3) (x 1) with h24 | h24
            ·
              rcases le_total (x 4) (x 0) with h25 | h25
              ·
                rcases le_total (x 4) (x 2) with h26 | h26
                ·
                  rcases le_total (x 4) (x 1) with h27 | h27
                  ·
                    rcases le_total (x 4) (x 3) with h28 | h28
                    ·
                      exact chamber6 x (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28])
                    ·
                      exact chamber7 x (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27,h28])
                  ·
                    exact chamber10 x (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26,h27])
                ·
                  exact chamber20 x (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26]) (by linarith only [h0,h1,h2,h22,h23,h24,h25,h26])
              ·
                exact chamber98 x (by linarith only [h0,h1,h2,h22,h23,h24,h25]) (by linarith only [h0,h1,h2,h22,h23,h24,h25]) (by linarith only [h0,h1,h2,h22,h23,h24,h25]) (by linarith only [h0,h1,h2,h22,h23,h24,h25])
            ·
              rcases le_total (x 4) (x 0) with h29 | h29
              ·
                rcases le_total (x 4) (x 2) with h30 | h30
                ·
                  rcases le_total (x 4) (x 3) with h31 | h31
                  ·
                    rcases le_total (x 4) (x 1) with h32 | h32
                    ·
                      exact chamber8 x (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32])
                    ·
                      exact chamber9 x (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31,h32])
                  ·
                    exact chamber11 x (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30,h31])
                ·
                  exact chamber21 x (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30]) (by linarith only [h0,h1,h2,h22,h23,h24,h29,h30])
              ·
                exact chamber99 x (by linarith only [h0,h1,h2,h22,h23,h24,h29]) (by linarith only [h0,h1,h2,h22,h23,h24,h29]) (by linarith only [h0,h1,h2,h22,h23,h24,h29]) (by linarith only [h0,h1,h2,h22,h23,h24,h29])
          ·
            rcases le_total (x 4) (x 0) with h33 | h33
            ·
              rcases le_total (x 4) (x 3) with h34 | h34
              ·
                rcases le_total (x 4) (x 2) with h35 | h35
                ·
                  rcases le_total (x 4) (x 1) with h36 | h36
                  ·
                    exact chamber14 x (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36])
                  ·
                    exact chamber15 x (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35,h36])
                ·
                  exact chamber17 x (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35]) (by linarith only [h0,h1,h2,h22,h23,h33,h34,h35])
              ·
                exact chamber23 x (by linarith only [h0,h1,h2,h22,h23,h33,h34]) (by linarith only [h0,h1,h2,h22,h23,h33,h34]) (by linarith only [h0,h1,h2,h22,h23,h33,h34]) (by linarith only [h0,h1,h2,h22,h23,h33,h34])
            ·
              exact chamber101 x (by linarith only [h0,h1,h2,h22,h23,h33]) (by linarith only [h0,h1,h2,h22,h23,h33]) (by linarith only [h0,h1,h2,h22,h23,h33]) (by linarith only [h0,h1,h2,h22,h23,h33])
        ·
          rcases le_total (x 4) (x 3) with h37 | h37
          ·
            rcases le_total (x 4) (x 0) with h38 | h38
            ·
              rcases le_total (x 4) (x 2) with h39 | h39
              ·
                rcases le_total (x 4) (x 1) with h40 | h40
                ·
                  exact chamber74 x (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40]) (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40]) (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40]) (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40])
                ·
                  exact chamber75 x (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40]) (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40]) (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40]) (by linarith only [h0,h1,h2,h22,h37,h38,h39,h40])
              ·
                exact chamber77 x (by linarith only [h0,h1,h2,h22,h37,h38,h39]) (by linarith only [h0,h1,h2,h22,h37,h38,h39]) (by linarith only [h0,h1,h2,h22,h37,h38,h39]) (by linarith only [h0,h1,h2,h22,h37,h38,h39])
            ·
              exact chamber91 x (by linarith only [h0,h1,h2,h22,h37,h38]) (by linarith only [h0,h1,h2,h22,h37,h38]) (by linarith only [h0,h1,h2,h22,h37,h38]) (by linarith only [h0,h1,h2,h22,h37,h38])
          ·
            exact chamber115 x (by linarith only [h0,h1,h2,h22,h37]) (by linarith only [h0,h1,h2,h22,h37]) (by linarith only [h0,h1,h2,h22,h37]) (by linarith only [h0,h1,h2,h22,h37])
    ·
      rcases le_total (x 3) (x 2) with h41 | h41
      ·
        rcases le_total (x 3) (x 0) with h42 | h42
        ·
          rcases le_total (x 3) (x 1) with h43 | h43
          ·
            rcases le_total (x 4) (x 2) with h44 | h44
            ·
              rcases le_total (x 4) (x 0) with h45 | h45
              ·
                rcases le_total (x 4) (x 1) with h46 | h46
                ·
                  rcases le_total (x 4) (x 3) with h47 | h47
                  ·
                    exact chamber48 x (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47])
                  ·
                    exact chamber49 x (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46,h47])
                ·
                  exact chamber52 x (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46]) (by linarith only [h0,h1,h41,h42,h43,h44,h45,h46])
              ·
                exact chamber66 x (by linarith only [h0,h1,h41,h42,h43,h44,h45]) (by linarith only [h0,h1,h41,h42,h43,h44,h45]) (by linarith only [h0,h1,h41,h42,h43,h44,h45]) (by linarith only [h0,h1,h41,h42,h43,h44,h45])
            ·
              exact chamber108 x (by linarith only [h0,h1,h41,h42,h43,h44]) (by linarith only [h0,h1,h41,h42,h43,h44]) (by linarith only [h0,h1,h41,h42,h43,h44]) (by linarith only [h0,h1,h41,h42,h43,h44])
          ·
            rcases le_total (x 4) (x 2) with h48 | h48
            ·
              rcases le_total (x 4) (x 0) with h49 | h49
              ·
                rcases le_total (x 4) (x 3) with h50 | h50
                ·
                  rcases le_total (x 4) (x 1) with h51 | h51
                  ·
                    exact chamber50 x (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51])
                  ·
                    exact chamber51 x (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50,h51])
                ·
                  exact chamber53 x (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50]) (by linarith only [h0,h1,h41,h42,h43,h48,h49,h50])
              ·
                exact chamber67 x (by linarith only [h0,h1,h41,h42,h43,h48,h49]) (by linarith only [h0,h1,h41,h42,h43,h48,h49]) (by linarith only [h0,h1,h41,h42,h43,h48,h49]) (by linarith only [h0,h1,h41,h42,h43,h48,h49])
            ·
              exact chamber109 x (by linarith only [h0,h1,h41,h42,h43,h48]) (by linarith only [h0,h1,h41,h42,h43,h48]) (by linarith only [h0,h1,h41,h42,h43,h48]) (by linarith only [h0,h1,h41,h42,h43,h48])
        ·
          rcases le_total (x 4) (x 2) with h52 | h52
          ·
            rcases le_total (x 4) (x 3) with h53 | h53
            ·
              rcases le_total (x 4) (x 0) with h54 | h54
              ·
                rcases le_total (x 4) (x 1) with h55 | h55
                ·
                  exact chamber60 x (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55]) (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55]) (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55]) (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55])
                ·
                  exact chamber61 x (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55]) (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55]) (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55]) (by linarith only [h0,h1,h41,h42,h52,h53,h54,h55])
              ·
                exact chamber64 x (by linarith only [h0,h1,h41,h42,h52,h53,h54]) (by linarith only [h0,h1,h41,h42,h52,h53,h54]) (by linarith only [h0,h1,h41,h42,h52,h53,h54]) (by linarith only [h0,h1,h41,h42,h52,h53,h54])
            ·
              exact chamber70 x (by linarith only [h0,h1,h41,h42,h52,h53]) (by linarith only [h0,h1,h41,h42,h52,h53]) (by linarith only [h0,h1,h41,h42,h52,h53]) (by linarith only [h0,h1,h41,h42,h52,h53])
          ·
            exact chamber112 x (by linarith only [h0,h1,h41,h42,h52]) (by linarith only [h0,h1,h41,h42,h52]) (by linarith only [h0,h1,h41,h42,h52]) (by linarith only [h0,h1,h41,h42,h52])
      ·
        rcases le_total (x 4) (x 3) with h56 | h56
        ·
          rcases le_total (x 4) (x 2) with h57 | h57
          ·
            rcases le_total (x 4) (x 0) with h58 | h58
            ·
              rcases le_total (x 4) (x 1) with h59 | h59
              ·
                exact chamber84 x (by linarith only [h0,h1,h41,h56,h57,h58,h59]) (by linarith only [h0,h1,h41,h56,h57,h58,h59]) (by linarith only [h0,h1,h41,h56,h57,h58,h59]) (by linarith only [h0,h1,h41,h56,h57,h58,h59])
              ·
                exact chamber85 x (by linarith only [h0,h1,h41,h56,h57,h58,h59]) (by linarith only [h0,h1,h41,h56,h57,h58,h59]) (by linarith only [h0,h1,h41,h56,h57,h58,h59]) (by linarith only [h0,h1,h41,h56,h57,h58,h59])
            ·
              exact chamber88 x (by linarith only [h0,h1,h41,h56,h57,h58]) (by linarith only [h0,h1,h41,h56,h57,h58]) (by linarith only [h0,h1,h41,h56,h57,h58]) (by linarith only [h0,h1,h41,h56,h57,h58])
          ·
            exact chamber94 x (by linarith only [h0,h1,h41,h56,h57]) (by linarith only [h0,h1,h41,h56,h57]) (by linarith only [h0,h1,h41,h56,h57]) (by linarith only [h0,h1,h41,h56,h57])
        ·
          exact chamber118 x (by linarith only [h0,h1,h41,h56]) (by linarith only [h0,h1,h41,h56]) (by linarith only [h0,h1,h41,h56]) (by linarith only [h0,h1,h41,h56])
  ·
    rcases le_total (x 2) (x 1) with h60 | h60
    ·
      rcases le_total (x 2) (x 0) with h61 | h61
      ·
        rcases le_total (x 3) (x 1) with h62 | h62
        ·
          rcases le_total (x 3) (x 0) with h63 | h63
          ·
            rcases le_total (x 3) (x 2) with h64 | h64
            ·
              rcases le_total (x 4) (x 1) with h65 | h65
              ·
                rcases le_total (x 4) (x 0) with h66 | h66
                ·
                  rcases le_total (x 4) (x 2) with h67 | h67
                  ·
                    rcases le_total (x 4) (x 3) with h68 | h68
                    ·
                      exact chamber24 x (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68])
                    ·
                      exact chamber25 x (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67,h68])
                  ·
                    exact chamber28 x (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66,h67])
                ·
                  exact chamber42 x (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66]) (by linarith only [h0,h60,h61,h62,h63,h64,h65,h66])
              ·
                exact chamber102 x (by linarith only [h0,h60,h61,h62,h63,h64,h65]) (by linarith only [h0,h60,h61,h62,h63,h64,h65]) (by linarith only [h0,h60,h61,h62,h63,h64,h65]) (by linarith only [h0,h60,h61,h62,h63,h64,h65])
            ·
              rcases le_total (x 4) (x 1) with h69 | h69
              ·
                rcases le_total (x 4) (x 0) with h70 | h70
                ·
                  rcases le_total (x 4) (x 3) with h71 | h71
                  ·
                    rcases le_total (x 4) (x 2) with h72 | h72
                    ·
                      exact chamber26 x (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72])
                    ·
                      exact chamber27 x (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71,h72])
                  ·
                    exact chamber29 x (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70,h71])
                ·
                  exact chamber43 x (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70]) (by linarith only [h0,h60,h61,h62,h63,h64,h69,h70])
              ·
                exact chamber103 x (by linarith only [h0,h60,h61,h62,h63,h64,h69]) (by linarith only [h0,h60,h61,h62,h63,h64,h69]) (by linarith only [h0,h60,h61,h62,h63,h64,h69]) (by linarith only [h0,h60,h61,h62,h63,h64,h69])
          ·
            rcases le_total (x 4) (x 1) with h73 | h73
            ·
              rcases le_total (x 4) (x 3) with h74 | h74
              ·
                rcases le_total (x 4) (x 0) with h75 | h75
                ·
                  rcases le_total (x 4) (x 2) with h76 | h76
                  ·
                    exact chamber36 x (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76])
                  ·
                    exact chamber37 x (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75,h76])
                ·
                  exact chamber40 x (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75]) (by linarith only [h0,h60,h61,h62,h63,h73,h74,h75])
              ·
                exact chamber46 x (by linarith only [h0,h60,h61,h62,h63,h73,h74]) (by linarith only [h0,h60,h61,h62,h63,h73,h74]) (by linarith only [h0,h60,h61,h62,h63,h73,h74]) (by linarith only [h0,h60,h61,h62,h63,h73,h74])
            ·
              exact chamber106 x (by linarith only [h0,h60,h61,h62,h63,h73]) (by linarith only [h0,h60,h61,h62,h63,h73]) (by linarith only [h0,h60,h61,h62,h63,h73]) (by linarith only [h0,h60,h61,h62,h63,h73])
        ·
          rcases le_total (x 4) (x 3) with h77 | h77
          ·
            rcases le_total (x 4) (x 1) with h78 | h78
            ·
              rcases le_total (x 4) (x 0) with h79 | h79
              ·
                rcases le_total (x 4) (x 2) with h80 | h80
                ·
                  exact chamber78 x (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80]) (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80]) (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80]) (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80])
                ·
                  exact chamber79 x (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80]) (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80]) (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80]) (by linarith only [h0,h60,h61,h62,h77,h78,h79,h80])
              ·
                exact chamber82 x (by linarith only [h0,h60,h61,h62,h77,h78,h79]) (by linarith only [h0,h60,h61,h62,h77,h78,h79]) (by linarith only [h0,h60,h61,h62,h77,h78,h79]) (by linarith only [h0,h60,h61,h62,h77,h78,h79])
            ·
              exact chamber92 x (by linarith only [h0,h60,h61,h62,h77,h78]) (by linarith only [h0,h60,h61,h62,h77,h78]) (by linarith only [h0,h60,h61,h62,h77,h78]) (by linarith only [h0,h60,h61,h62,h77,h78])
          ·
            exact chamber116 x (by linarith only [h0,h60,h61,h62,h77]) (by linarith only [h0,h60,h61,h62,h77]) (by linarith only [h0,h60,h61,h62,h77]) (by linarith only [h0,h60,h61,h62,h77])
      ·
        rcases le_total (x 3) (x 1) with h81 | h81
        ·
          rcases le_total (x 3) (x 2) with h82 | h82
          ·
            rcases le_total (x 3) (x 0) with h83 | h83
            ·
              rcases le_total (x 4) (x 1) with h84 | h84
              ·
                rcases le_total (x 4) (x 2) with h85 | h85
                ·
                  rcases le_total (x 4) (x 0) with h86 | h86
                  ·
                    rcases le_total (x 4) (x 3) with h87 | h87
                    ·
                      exact chamber30 x (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87])
                    ·
                      exact chamber31 x (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86,h87])
                  ·
                    exact chamber34 x (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85,h86])
                ·
                  exact chamber44 x (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85]) (by linarith only [h0,h60,h61,h81,h82,h83,h84,h85])
              ·
                exact chamber104 x (by linarith only [h0,h60,h61,h81,h82,h83,h84]) (by linarith only [h0,h60,h61,h81,h82,h83,h84]) (by linarith only [h0,h60,h61,h81,h82,h83,h84]) (by linarith only [h0,h60,h61,h81,h82,h83,h84])
            ·
              rcases le_total (x 4) (x 1) with h88 | h88
              ·
                rcases le_total (x 4) (x 2) with h89 | h89
                ·
                  rcases le_total (x 4) (x 3) with h90 | h90
                  ·
                    rcases le_total (x 4) (x 0) with h91 | h91
                    ·
                      exact chamber32 x (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91])
                    ·
                      exact chamber33 x (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90,h91])
                  ·
                    exact chamber35 x (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89,h90])
                ·
                  exact chamber45 x (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89]) (by linarith only [h0,h60,h61,h81,h82,h83,h88,h89])
              ·
                exact chamber105 x (by linarith only [h0,h60,h61,h81,h82,h83,h88]) (by linarith only [h0,h60,h61,h81,h82,h83,h88]) (by linarith only [h0,h60,h61,h81,h82,h83,h88]) (by linarith only [h0,h60,h61,h81,h82,h83,h88])
          ·
            rcases le_total (x 4) (x 1) with h92 | h92
            ·
              rcases le_total (x 4) (x 3) with h93 | h93
              ·
                rcases le_total (x 4) (x 2) with h94 | h94
                ·
                  rcases le_total (x 4) (x 0) with h95 | h95
                  ·
                    exact chamber38 x (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95])
                  ·
                    exact chamber39 x (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94,h95])
                ·
                  exact chamber41 x (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94]) (by linarith only [h0,h60,h61,h81,h82,h92,h93,h94])
              ·
                exact chamber47 x (by linarith only [h0,h60,h61,h81,h82,h92,h93]) (by linarith only [h0,h60,h61,h81,h82,h92,h93]) (by linarith only [h0,h60,h61,h81,h82,h92,h93]) (by linarith only [h0,h60,h61,h81,h82,h92,h93])
            ·
              exact chamber107 x (by linarith only [h0,h60,h61,h81,h82,h92]) (by linarith only [h0,h60,h61,h81,h82,h92]) (by linarith only [h0,h60,h61,h81,h82,h92]) (by linarith only [h0,h60,h61,h81,h82,h92])
        ·
          rcases le_total (x 4) (x 3) with h96 | h96
          ·
            rcases le_total (x 4) (x 1) with h97 | h97
            ·
              rcases le_total (x 4) (x 2) with h98 | h98
              ·
                rcases le_total (x 4) (x 0) with h99 | h99
                ·
                  exact chamber80 x (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99]) (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99]) (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99]) (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99])
                ·
                  exact chamber81 x (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99]) (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99]) (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99]) (by linarith only [h0,h60,h61,h81,h96,h97,h98,h99])
              ·
                exact chamber83 x (by linarith only [h0,h60,h61,h81,h96,h97,h98]) (by linarith only [h0,h60,h61,h81,h96,h97,h98]) (by linarith only [h0,h60,h61,h81,h96,h97,h98]) (by linarith only [h0,h60,h61,h81,h96,h97,h98])
            ·
              exact chamber93 x (by linarith only [h0,h60,h61,h81,h96,h97]) (by linarith only [h0,h60,h61,h81,h96,h97]) (by linarith only [h0,h60,h61,h81,h96,h97]) (by linarith only [h0,h60,h61,h81,h96,h97])
          ·
            exact chamber117 x (by linarith only [h0,h60,h61,h81,h96]) (by linarith only [h0,h60,h61,h81,h96]) (by linarith only [h0,h60,h61,h81,h96]) (by linarith only [h0,h60,h61,h81,h96])
    ·
      rcases le_total (x 3) (x 2) with h100 | h100
      ·
        rcases le_total (x 3) (x 1) with h101 | h101
        ·
          rcases le_total (x 3) (x 0) with h102 | h102
          ·
            rcases le_total (x 4) (x 2) with h103 | h103
            ·
              rcases le_total (x 4) (x 1) with h104 | h104
              ·
                rcases le_total (x 4) (x 0) with h105 | h105
                ·
                  rcases le_total (x 4) (x 3) with h106 | h106
                  ·
                    exact chamber54 x (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106])
                  ·
                    exact chamber55 x (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105,h106])
                ·
                  exact chamber58 x (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105]) (by linarith only [h0,h60,h100,h101,h102,h103,h104,h105])
              ·
                exact chamber68 x (by linarith only [h0,h60,h100,h101,h102,h103,h104]) (by linarith only [h0,h60,h100,h101,h102,h103,h104]) (by linarith only [h0,h60,h100,h101,h102,h103,h104]) (by linarith only [h0,h60,h100,h101,h102,h103,h104])
            ·
              exact chamber110 x (by linarith only [h0,h60,h100,h101,h102,h103]) (by linarith only [h0,h60,h100,h101,h102,h103]) (by linarith only [h0,h60,h100,h101,h102,h103]) (by linarith only [h0,h60,h100,h101,h102,h103])
          ·
            rcases le_total (x 4) (x 2) with h107 | h107
            ·
              rcases le_total (x 4) (x 1) with h108 | h108
              ·
                rcases le_total (x 4) (x 3) with h109 | h109
                ·
                  rcases le_total (x 4) (x 0) with h110 | h110
                  ·
                    exact chamber56 x (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110])
                  ·
                    exact chamber57 x (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109,h110])
                ·
                  exact chamber59 x (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109]) (by linarith only [h0,h60,h100,h101,h102,h107,h108,h109])
              ·
                exact chamber69 x (by linarith only [h0,h60,h100,h101,h102,h107,h108]) (by linarith only [h0,h60,h100,h101,h102,h107,h108]) (by linarith only [h0,h60,h100,h101,h102,h107,h108]) (by linarith only [h0,h60,h100,h101,h102,h107,h108])
            ·
              exact chamber111 x (by linarith only [h0,h60,h100,h101,h102,h107]) (by linarith only [h0,h60,h100,h101,h102,h107]) (by linarith only [h0,h60,h100,h101,h102,h107]) (by linarith only [h0,h60,h100,h101,h102,h107])
        ·
          rcases le_total (x 4) (x 2) with h111 | h111
          ·
            rcases le_total (x 4) (x 3) with h112 | h112
            ·
              rcases le_total (x 4) (x 1) with h113 | h113
              ·
                rcases le_total (x 4) (x 0) with h114 | h114
                ·
                  exact chamber62 x (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114]) (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114]) (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114]) (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114])
                ·
                  exact chamber63 x (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114]) (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114]) (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114]) (by linarith only [h0,h60,h100,h101,h111,h112,h113,h114])
              ·
                exact chamber65 x (by linarith only [h0,h60,h100,h101,h111,h112,h113]) (by linarith only [h0,h60,h100,h101,h111,h112,h113]) (by linarith only [h0,h60,h100,h101,h111,h112,h113]) (by linarith only [h0,h60,h100,h101,h111,h112,h113])
            ·
              exact chamber71 x (by linarith only [h0,h60,h100,h101,h111,h112]) (by linarith only [h0,h60,h100,h101,h111,h112]) (by linarith only [h0,h60,h100,h101,h111,h112]) (by linarith only [h0,h60,h100,h101,h111,h112])
          ·
            exact chamber113 x (by linarith only [h0,h60,h100,h101,h111]) (by linarith only [h0,h60,h100,h101,h111]) (by linarith only [h0,h60,h100,h101,h111]) (by linarith only [h0,h60,h100,h101,h111])
      ·
        rcases le_total (x 4) (x 3) with h115 | h115
        ·
          rcases le_total (x 4) (x 2) with h116 | h116
          ·
            rcases le_total (x 4) (x 1) with h117 | h117
            ·
              rcases le_total (x 4) (x 0) with h118 | h118
              ·
                exact chamber86 x (by linarith only [h0,h60,h100,h115,h116,h117,h118]) (by linarith only [h0,h60,h100,h115,h116,h117,h118]) (by linarith only [h0,h60,h100,h115,h116,h117,h118]) (by linarith only [h0,h60,h100,h115,h116,h117,h118])
              ·
                exact chamber87 x (by linarith only [h0,h60,h100,h115,h116,h117,h118]) (by linarith only [h0,h60,h100,h115,h116,h117,h118]) (by linarith only [h0,h60,h100,h115,h116,h117,h118]) (by linarith only [h0,h60,h100,h115,h116,h117,h118])
            ·
              exact chamber89 x (by linarith only [h0,h60,h100,h115,h116,h117]) (by linarith only [h0,h60,h100,h115,h116,h117]) (by linarith only [h0,h60,h100,h115,h116,h117]) (by linarith only [h0,h60,h100,h115,h116,h117])
          ·
            exact chamber95 x (by linarith only [h0,h60,h100,h115,h116]) (by linarith only [h0,h60,h100,h115,h116]) (by linarith only [h0,h60,h100,h115,h116]) (by linarith only [h0,h60,h100,h115,h116])
        ·
          exact chamber119 x (by linarith only [h0,h60,h100,h115]) (by linarith only [h0,h60,h100,h115]) (by linarith only [h0,h60,h100,h115]) (by linarith only [h0,h60,h100,h115])

end MaxCaterpillar.WidthTradeoff.P4
