import Erdos1183.Window20Data

/-!
# The listed sublattices are sublattices

Each of the `32` parts of `gadgets` is checked by evaluation in the kernel; the parts are kept
separate so that each check stays small.
-/

namespace Erdos1183.W20

set_option maxRecDepth 100000 in
theorem gsub_0_ok : gsub_0.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_1_ok : gsub_1.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_2_ok : gsub_2.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_3_ok : gsub_3.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_4_ok : gsub_4.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_5_ok : gsub_5.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_6_ok : gsub_6.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_7_ok : gsub_7.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_8_ok : gsub_8.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_9_ok : gsub_9.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_10_ok : gsub_10.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_11_ok : gsub_11.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_12_ok : gsub_12.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_13_ok : gsub_13.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_14_ok : gsub_14.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_15_ok : gsub_15.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_16_ok : gsub_16.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_17_ok : gsub_17.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_18_ok : gsub_18.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_19_ok : gsub_19.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_20_ok : gsub_20.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_21_ok : gsub_21.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_22_ok : gsub_22.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_23_ok : gsub_23.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_24_ok : gsub_24.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_25_ok : gsub_25.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_26_ok : gsub_26.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_27_ok : gsub_27.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_28_ok : gsub_28.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_29_ok : gsub_29.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_30_ok : gsub_30.allOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gsub_31_ok : gsub_31.allOk = true := by decide +kernel

/-- Every listed family is a sublattice of its cube with the stated sizes. -/
theorem gadgets_ok : gadgets.allOk = true := by
  simp only [gadgets, GTree.allOk, gsub_0_ok, gsub_1_ok, gsub_2_ok, gsub_3_ok, gsub_4_ok, gsub_5_ok,
    gsub_6_ok, gsub_7_ok, gsub_8_ok, gsub_9_ok, gsub_10_ok, gsub_11_ok, gsub_12_ok, gsub_13_ok,
    gsub_14_ok, gsub_15_ok, gsub_16_ok, gsub_17_ok, gsub_18_ok, gsub_19_ok, gsub_20_ok, gsub_21_ok,
    gsub_22_ok, gsub_23_ok, gsub_24_ok, gsub_25_ok, gsub_26_ok, gsub_27_ok, gsub_28_ok, gsub_29_ok,
    gsub_30_ok, gsub_31_ok, Bool.and_self]

end Erdos1183.W20
