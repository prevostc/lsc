import Lsc.Lib.Math.SqrtRef
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases

namespace Lsc.Math.OzCertHi
open Lsc.Math.SqrtRef
theorem chunk_131072_139263 (n : Nat) (h : n ≤ 139263) (h' : 131072 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_139264_147455 (n : Nat) (h : n ≤ 147455) (h' : 139264 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_147456_155647 (n : Nat) (h : n ≤ 155647) (h' : 147456 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_155648_163839 (n : Nat) (h : n ≤ 163839) (h' : 155648 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_163840_172031 (n : Nat) (h : n ≤ 172031) (h' : 163840 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_172032_180223 (n : Nat) (h : n ≤ 180223) (h' : 172032 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_180224_188415 (n : Nat) (h : n ≤ 188415) (h' : 180224 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_188416_196607 (n : Nat) (h : n ≤ 196607) (h' : 188416 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_196608_204799 (n : Nat) (h : n ≤ 204799) (h' : 196608 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_204800_212991 (n : Nat) (h : n ≤ 212991) (h' : 204800 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_212992_221183 (n : Nat) (h : n ≤ 221183) (h' : 212992 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_221184_229375 (n : Nat) (h : n ≤ 229375) (h' : 221184 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_229376_237567 (n : Nat) (h : n ≤ 237567) (h' : 229376 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_237568_245759 (n : Nat) (h : n ≤ 245759) (h' : 237568 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_245760_253951 (n : Nat) (h : n ≤ 253951) (h' : 245760 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_253952_262143 (n : Nat) (h : n ≤ 262143) (h' : 253952 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide

theorem ozSqrtEvm_le262143 (n : Nat) (hn : n ≤ 262143) (hb : 131072 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  by_cases h0 : n ≤ 139263
  · exact chunk_131072_139263 n h0 (by omega)
  by_cases h1 : n ≤ 147455
  · exact chunk_139264_147455 n h1 (by omega)
  by_cases h2 : n ≤ 155647
  · exact chunk_147456_155647 n h2 (by omega)
  by_cases h3 : n ≤ 163839
  · exact chunk_155648_163839 n h3 (by omega)
  by_cases h4 : n ≤ 172031
  · exact chunk_163840_172031 n h4 (by omega)
  by_cases h5 : n ≤ 180223
  · exact chunk_172032_180223 n h5 (by omega)
  by_cases h6 : n ≤ 188415
  · exact chunk_180224_188415 n h6 (by omega)
  by_cases h7 : n ≤ 196607
  · exact chunk_188416_196607 n h7 (by omega)
  by_cases h8 : n ≤ 204799
  · exact chunk_196608_204799 n h8 (by omega)
  by_cases h9 : n ≤ 212991
  · exact chunk_204800_212991 n h9 (by omega)
  by_cases h10 : n ≤ 221183
  · exact chunk_212992_221183 n h10 (by omega)
  by_cases h11 : n ≤ 229375
  · exact chunk_221184_229375 n h11 (by omega)
  by_cases h12 : n ≤ 237567
  · exact chunk_229376_237567 n h12 (by omega)
  by_cases h13 : n ≤ 245759
  · exact chunk_237568_245759 n h13 (by omega)
  by_cases h14 : n ≤ 253951
  · exact chunk_245760_253951 n h14 (by omega)
  by_cases h15 : n ≤ 262143
  · exact chunk_253952_262143 n h15 (by omega)
  · omega
end Lsc.Math.OzCertHi
