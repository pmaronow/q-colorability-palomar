import ThLean.BP.S5.Exports

namespace ThLean.BP.S5

example (ha : S5_17AStatement) (hb : S5_17BStatement)
    (hc : S5_17CStatement) : S5_17Statement :=
  S5_17_assembly ha hb hc

example (h19 : S5_19Statement) (h22 : S5_22Statement)
    (ha : S5_26AStatement) (hb : S5_26BStatement) (hc : S5_26CStatement) :
    S5_26Statement :=
  S5_26_assembly h19 h22 ha hb hc

example (ha : S5_33AStatement) (hb : S5_33BStatement) :
    S5_33Statement :=
  S5_33_assembly ha hb

example (ha : S5_34AStatement) (hb : S5_34BStatement)
    (h33 : S5_33Statement) : S5_34Statement :=
  S5_34_assembly ha hb h33

example (ha : S5_08AStatement) (hb : S5_08BStatement)
    (hc : S5_08CStatement) : S5_08Statement :=
  S5_08_assembly ha hb hc

example (ha : S5_09AStatement) (hb : S5_09BStatement)
    (hc : S5_09CStatement) : S5_09Statement :=
  S5_09_assembly ha hb hc

example (ha : S5_15AStatement) (hb : S5_15BStatement) :
    S5_15Statement :=
  S5_15_assembly ha hb

example (h11 : S5_11Statement) (h13 : S5_13AStatement) (h14 : S5_14Statement)
    (h15 : S5_15Statement) : S5_16Statement :=
  S5_16_assembly h11 h13 h14 h15

example (ha : S5_28AStatement) (hb : S5_28BStatement) :
    S5_28Statement :=
  S5_28_assembly ha hb

example (h05 : S5_05Statement) (h27 : S5_27Statement)
    (h28 : S5_28Statement) (ha : S5_29AStatement) : S5_29Statement :=
  S5_29_assembly h05 h27 h28 ha

example (ha : S5_E06AStatement) (hb : S5_E06BStatement) :
    S5_E06Statement :=
  S5_E06_assembly ha hb

example (h26 : S5_26Statement) (h36 : S5_36Statement)
    (h37 : S5_37Statement) (h38 : S5_38Statement) : S5_39Statement :=
  S5_39_assembly h26 h36 h37 h38

example (h34 : S5_34Statement) (h35 : S5_35Statement)
    (h36 : S5_36Statement) (h39 : S5_39Statement) (ha : S5_40AStatement) :
    S5_40Statement :=
  S5_40_assembly h34 h35 h36 h39 ha

example (h40 : S5_40Statement) (h41 : S5_41Statement)
    (ha : S5_42AStatement) : S5_42Statement :=
  S5_42_assembly h40 h41 ha

end ThLean.BP.S5
