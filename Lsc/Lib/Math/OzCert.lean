import Lsc.Lib.Math.SqrtRef
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases

namespace Lsc.Math.OzCert
open Lsc.Math.SqrtRef
theorem chunk_0_8191 (n : Nat) (h : n ≤ 8191) (h' : 0 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_8192_16383 (n : Nat) (h : n ≤ 16383) (h' : 8192 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_16384_24575 (n : Nat) (h : n ≤ 24575) (h' : 16384 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_24576_32767 (n : Nat) (h : n ≤ 32767) (h' : 24576 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_32768_40959 (n : Nat) (h : n ≤ 40959) (h' : 32768 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_40960_49151 (n : Nat) (h : n ≤ 49151) (h' : 40960 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_49152_57343 (n : Nat) (h : n ≤ 57343) (h' : 49152 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_57344_65535 (n : Nat) (h : n ≤ 65535) (h' : 57344 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_65536_73727 (n : Nat) (h : n ≤ 73727) (h' : 65536 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_73728_81919 (n : Nat) (h : n ≤ 81919) (h' : 73728 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_81920_90111 (n : Nat) (h : n ≤ 90111) (h' : 81920 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_90112_98303 (n : Nat) (h : n ≤ 98303) (h' : 90112 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_98304_106495 (n : Nat) (h : n ≤ 106495) (h' : 98304 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_106496_114687 (n : Nat) (h : n ≤ 114687) (h' : 106496 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_114688_122879 (n : Nat) (h : n ≤ 122879) (h' : 114688 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide
theorem chunk_122880_131071 (n : Nat) (h : n ≤ 131071) (h' : 122880 ≤ n) : ozSqrtEvm n = Nat.sqrt n := by
  interval_cases n <;> native_decide

theorem ozSqrtEvm_le131071 (n : Nat) (hn : n ≤ 131071) : ozSqrtEvm n = Nat.sqrt n := by
  by_cases h0 : n ≤ 8191
  · exact chunk_0_8191 n h0 (by omega)
  by_cases h1 : n ≤ 16383
  · exact chunk_8192_16383 n h1 (by omega)
  by_cases h2 : n ≤ 24575
  · exact chunk_16384_24575 n h2 (by omega)
  by_cases h3 : n ≤ 32767
  · exact chunk_24576_32767 n h3 (by omega)
  by_cases h4 : n ≤ 40959
  · exact chunk_32768_40959 n h4 (by omega)
  by_cases h5 : n ≤ 49151
  · exact chunk_40960_49151 n h5 (by omega)
  by_cases h6 : n ≤ 57343
  · exact chunk_49152_57343 n h6 (by omega)
  by_cases h7 : n ≤ 65535
  · exact chunk_57344_65535 n h7 (by omega)
  by_cases h8 : n ≤ 73727
  · exact chunk_65536_73727 n h8 (by omega)
  by_cases h9 : n ≤ 81919
  · exact chunk_73728_81919 n h9 (by omega)
  by_cases h10 : n ≤ 90111
  · exact chunk_81920_90111 n h10 (by omega)
  by_cases h11 : n ≤ 98303
  · exact chunk_90112_98303 n h11 (by omega)
  by_cases h12 : n ≤ 106495
  · exact chunk_98304_106495 n h12 (by omega)
  by_cases h13 : n ≤ 114687
  · exact chunk_106496_114687 n h13 (by omega)
  by_cases h14 : n ≤ 122879
  · exact chunk_114688_122879 n h14 (by omega)
  by_cases h15 : n ≤ 131071
  · exact chunk_122880_131071 n h15 (by omega)
  · omega
end Lsc.Math.OzCert
