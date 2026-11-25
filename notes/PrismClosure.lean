import PrismFrontierCertificate

namespace PrismSignedFrontier.Certificate

def span (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_member {f n o} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    intro i lo hi
    obtain ⟨first,tail⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.eq_or_lt_of_le lo with rfl | gt
    · exact first
    · exact ih tail i (by omega) (by omega)

theorem span_join {f a o b} (left : span f a o = true) (right : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using right
  | succ a ih =>
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp left
    rw [Nat.succ_add]
    exact Bool.and_eq_true_iff.mpr ⟨first,ih rest (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using right)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x16 : span (checked 4) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x32 : span (checked 4) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4x48 : span (checked 4) 14 48 = true := by decide +kernel

theorem layer4 : span (checked 4) 62 0 = true :=
  (@span_join (checked 4) 32 0 30 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 14 chunk4x32 chunk4x48))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x0 : span (checked 5) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x16 : span (checked 5) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x32 : span (checked 5) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x48 : span (checked 5) 16 48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x64 : span (checked 5) 16 64 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x80 : span (checked 5) 16 80 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x96 : span (checked 5) 16 96 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x112 : span (checked 5) 16 112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x128 : span (checked 5) 16 128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x144 : span (checked 5) 16 144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x160 : span (checked 5) 16 160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x176 : span (checked 5) 16 176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x192 : span (checked 5) 16 192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x208 : span (checked 5) 16 208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x224 : span (checked 5) 16 224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x240 : span (checked 5) 16 240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x256 : span (checked 5) 16 256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x272 : span (checked 5) 16 272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x288 : span (checked 5) 16 288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x304 : span (checked 5) 16 304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x320 : span (checked 5) 16 320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x336 : span (checked 5) 16 336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x352 : span (checked 5) 16 352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x368 : span (checked 5) 16 368 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x384 : span (checked 5) 16 384 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x400 : span (checked 5) 16 400 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x416 : span (checked 5) 16 416 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x432 : span (checked 5) 16 432 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x448 : span (checked 5) 16 448 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x464 : span (checked 5) 16 464 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x480 : span (checked 5) 16 480 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x496 : span (checked 5) 16 496 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x512 : span (checked 5) 16 512 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x528 : span (checked 5) 16 528 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x544 : span (checked 5) 16 544 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x560 : span (checked 5) 16 560 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x576 : span (checked 5) 16 576 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x592 : span (checked 5) 16 592 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x608 : span (checked 5) 16 608 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x624 : span (checked 5) 16 624 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x640 : span (checked 5) 16 640 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x656 : span (checked 5) 16 656 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x672 : span (checked 5) 16 672 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x688 : span (checked 5) 16 688 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x704 : span (checked 5) 16 704 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x720 : span (checked 5) 16 720 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x736 : span (checked 5) 16 736 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x752 : span (checked 5) 16 752 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x768 : span (checked 5) 16 768 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x784 : span (checked 5) 16 784 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x800 : span (checked 5) 16 800 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x816 : span (checked 5) 16 816 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x832 : span (checked 5) 16 832 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x848 : span (checked 5) 16 848 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x864 : span (checked 5) 16 864 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x880 : span (checked 5) 16 880 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x896 : span (checked 5) 16 896 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x912 : span (checked 5) 16 912 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x928 : span (checked 5) 16 928 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x944 : span (checked 5) 16 944 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x960 : span (checked 5) 16 960 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x976 : span (checked 5) 16 976 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x992 : span (checked 5) 16 992 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1008 : span (checked 5) 16 1008 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1024 : span (checked 5) 16 1024 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1040 : span (checked 5) 16 1040 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1056 : span (checked 5) 16 1056 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1072 : span (checked 5) 16 1072 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1088 : span (checked 5) 16 1088 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1104 : span (checked 5) 16 1104 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1120 : span (checked 5) 16 1120 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1136 : span (checked 5) 16 1136 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1152 : span (checked 5) 16 1152 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1168 : span (checked 5) 16 1168 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1184 : span (checked 5) 16 1184 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1200 : span (checked 5) 16 1200 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1216 : span (checked 5) 16 1216 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1232 : span (checked 5) 16 1232 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1248 : span (checked 5) 16 1248 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1264 : span (checked 5) 16 1264 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1280 : span (checked 5) 16 1280 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1296 : span (checked 5) 16 1296 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1312 : span (checked 5) 16 1312 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1328 : span (checked 5) 16 1328 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1344 : span (checked 5) 16 1344 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1360 : span (checked 5) 16 1360 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1376 : span (checked 5) 16 1376 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1392 : span (checked 5) 16 1392 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1408 : span (checked 5) 16 1408 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1424 : span (checked 5) 16 1424 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1440 : span (checked 5) 16 1440 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1456 : span (checked 5) 16 1456 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1472 : span (checked 5) 16 1472 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1488 : span (checked 5) 16 1488 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1504 : span (checked 5) 16 1504 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1520 : span (checked 5) 16 1520 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1536 : span (checked 5) 16 1536 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1552 : span (checked 5) 16 1552 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1568 : span (checked 5) 16 1568 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1584 : span (checked 5) 16 1584 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1600 : span (checked 5) 16 1600 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1616 : span (checked 5) 16 1616 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1632 : span (checked 5) 16 1632 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1648 : span (checked 5) 16 1648 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1664 : span (checked 5) 16 1664 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1680 : span (checked 5) 16 1680 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1696 : span (checked 5) 16 1696 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1712 : span (checked 5) 16 1712 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1728 : span (checked 5) 16 1728 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1744 : span (checked 5) 16 1744 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1760 : span (checked 5) 16 1760 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1776 : span (checked 5) 16 1776 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1792 : span (checked 5) 16 1792 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1808 : span (checked 5) 16 1808 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1824 : span (checked 5) 16 1824 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1840 : span (checked 5) 16 1840 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1856 : span (checked 5) 16 1856 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1872 : span (checked 5) 16 1872 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1888 : span (checked 5) 16 1888 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1904 : span (checked 5) 16 1904 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1920 : span (checked 5) 16 1920 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1936 : span (checked 5) 16 1936 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1952 : span (checked 5) 16 1952 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1968 : span (checked 5) 16 1968 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x1984 : span (checked 5) 16 1984 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk5x2000 : span (checked 5) 2 2000 = true := by decide +kernel

theorem layer5 : span (checked 5) 2002 0 = true :=
  (@span_join (checked 5) 1008 0 994 (@span_join (checked 5) 496 0 512 (@span_join (checked 5) 240 0 256 (@span_join (checked 5) 112 0 128 (@span_join (checked 5) 48 0 64 (@span_join (checked 5) 16 0 32 chunk5x0 (@span_join (checked 5) 16 16 16 chunk5x16 chunk5x32)) (@span_join (checked 5) 32 48 32 (@span_join (checked 5) 16 48 16 chunk5x48 chunk5x64) (@span_join (checked 5) 16 80 16 chunk5x80 chunk5x96))) (@span_join (checked 5) 64 112 64 (@span_join (checked 5) 32 112 32 (@span_join (checked 5) 16 112 16 chunk5x112 chunk5x128) (@span_join (checked 5) 16 144 16 chunk5x144 chunk5x160)) (@span_join (checked 5) 32 176 32 (@span_join (checked 5) 16 176 16 chunk5x176 chunk5x192) (@span_join (checked 5) 16 208 16 chunk5x208 chunk5x224)))) (@span_join (checked 5) 128 240 128 (@span_join (checked 5) 64 240 64 (@span_join (checked 5) 32 240 32 (@span_join (checked 5) 16 240 16 chunk5x240 chunk5x256) (@span_join (checked 5) 16 272 16 chunk5x272 chunk5x288)) (@span_join (checked 5) 32 304 32 (@span_join (checked 5) 16 304 16 chunk5x304 chunk5x320) (@span_join (checked 5) 16 336 16 chunk5x336 chunk5x352))) (@span_join (checked 5) 64 368 64 (@span_join (checked 5) 32 368 32 (@span_join (checked 5) 16 368 16 chunk5x368 chunk5x384) (@span_join (checked 5) 16 400 16 chunk5x400 chunk5x416)) (@span_join (checked 5) 32 432 32 (@span_join (checked 5) 16 432 16 chunk5x432 chunk5x448) (@span_join (checked 5) 16 464 16 chunk5x464 chunk5x480))))) (@span_join (checked 5) 256 496 256 (@span_join (checked 5) 128 496 128 (@span_join (checked 5) 64 496 64 (@span_join (checked 5) 32 496 32 (@span_join (checked 5) 16 496 16 chunk5x496 chunk5x512) (@span_join (checked 5) 16 528 16 chunk5x528 chunk5x544)) (@span_join (checked 5) 32 560 32 (@span_join (checked 5) 16 560 16 chunk5x560 chunk5x576) (@span_join (checked 5) 16 592 16 chunk5x592 chunk5x608))) (@span_join (checked 5) 64 624 64 (@span_join (checked 5) 32 624 32 (@span_join (checked 5) 16 624 16 chunk5x624 chunk5x640) (@span_join (checked 5) 16 656 16 chunk5x656 chunk5x672)) (@span_join (checked 5) 32 688 32 (@span_join (checked 5) 16 688 16 chunk5x688 chunk5x704) (@span_join (checked 5) 16 720 16 chunk5x720 chunk5x736)))) (@span_join (checked 5) 128 752 128 (@span_join (checked 5) 64 752 64 (@span_join (checked 5) 32 752 32 (@span_join (checked 5) 16 752 16 chunk5x752 chunk5x768) (@span_join (checked 5) 16 784 16 chunk5x784 chunk5x800)) (@span_join (checked 5) 32 816 32 (@span_join (checked 5) 16 816 16 chunk5x816 chunk5x832) (@span_join (checked 5) 16 848 16 chunk5x848 chunk5x864))) (@span_join (checked 5) 64 880 64 (@span_join (checked 5) 32 880 32 (@span_join (checked 5) 16 880 16 chunk5x880 chunk5x896) (@span_join (checked 5) 16 912 16 chunk5x912 chunk5x928)) (@span_join (checked 5) 32 944 32 (@span_join (checked 5) 16 944 16 chunk5x944 chunk5x960) (@span_join (checked 5) 16 976 16 chunk5x976 chunk5x992)))))) (@span_join (checked 5) 496 1008 498 (@span_join (checked 5) 240 1008 256 (@span_join (checked 5) 112 1008 128 (@span_join (checked 5) 48 1008 64 (@span_join (checked 5) 16 1008 32 chunk5x1008 (@span_join (checked 5) 16 1024 16 chunk5x1024 chunk5x1040)) (@span_join (checked 5) 32 1056 32 (@span_join (checked 5) 16 1056 16 chunk5x1056 chunk5x1072) (@span_join (checked 5) 16 1088 16 chunk5x1088 chunk5x1104))) (@span_join (checked 5) 64 1120 64 (@span_join (checked 5) 32 1120 32 (@span_join (checked 5) 16 1120 16 chunk5x1120 chunk5x1136) (@span_join (checked 5) 16 1152 16 chunk5x1152 chunk5x1168)) (@span_join (checked 5) 32 1184 32 (@span_join (checked 5) 16 1184 16 chunk5x1184 chunk5x1200) (@span_join (checked 5) 16 1216 16 chunk5x1216 chunk5x1232)))) (@span_join (checked 5) 128 1248 128 (@span_join (checked 5) 64 1248 64 (@span_join (checked 5) 32 1248 32 (@span_join (checked 5) 16 1248 16 chunk5x1248 chunk5x1264) (@span_join (checked 5) 16 1280 16 chunk5x1280 chunk5x1296)) (@span_join (checked 5) 32 1312 32 (@span_join (checked 5) 16 1312 16 chunk5x1312 chunk5x1328) (@span_join (checked 5) 16 1344 16 chunk5x1344 chunk5x1360))) (@span_join (checked 5) 64 1376 64 (@span_join (checked 5) 32 1376 32 (@span_join (checked 5) 16 1376 16 chunk5x1376 chunk5x1392) (@span_join (checked 5) 16 1408 16 chunk5x1408 chunk5x1424)) (@span_join (checked 5) 32 1440 32 (@span_join (checked 5) 16 1440 16 chunk5x1440 chunk5x1456) (@span_join (checked 5) 16 1472 16 chunk5x1472 chunk5x1488))))) (@span_join (checked 5) 256 1504 242 (@span_join (checked 5) 128 1504 128 (@span_join (checked 5) 64 1504 64 (@span_join (checked 5) 32 1504 32 (@span_join (checked 5) 16 1504 16 chunk5x1504 chunk5x1520) (@span_join (checked 5) 16 1536 16 chunk5x1536 chunk5x1552)) (@span_join (checked 5) 32 1568 32 (@span_join (checked 5) 16 1568 16 chunk5x1568 chunk5x1584) (@span_join (checked 5) 16 1600 16 chunk5x1600 chunk5x1616))) (@span_join (checked 5) 64 1632 64 (@span_join (checked 5) 32 1632 32 (@span_join (checked 5) 16 1632 16 chunk5x1632 chunk5x1648) (@span_join (checked 5) 16 1664 16 chunk5x1664 chunk5x1680)) (@span_join (checked 5) 32 1696 32 (@span_join (checked 5) 16 1696 16 chunk5x1696 chunk5x1712) (@span_join (checked 5) 16 1728 16 chunk5x1728 chunk5x1744)))) (@span_join (checked 5) 128 1760 114 (@span_join (checked 5) 64 1760 64 (@span_join (checked 5) 32 1760 32 (@span_join (checked 5) 16 1760 16 chunk5x1760 chunk5x1776) (@span_join (checked 5) 16 1792 16 chunk5x1792 chunk5x1808)) (@span_join (checked 5) 32 1824 32 (@span_join (checked 5) 16 1824 16 chunk5x1824 chunk5x1840) (@span_join (checked 5) 16 1856 16 chunk5x1856 chunk5x1872))) (@span_join (checked 5) 64 1888 50 (@span_join (checked 5) 32 1888 32 (@span_join (checked 5) 16 1888 16 chunk5x1888 chunk5x1904) (@span_join (checked 5) 16 1920 16 chunk5x1920 chunk5x1936)) (@span_join (checked 5) 32 1952 18 (@span_join (checked 5) 16 1952 16 chunk5x1952 chunk5x1968) (@span_join (checked 5) 16 1984 2 chunk5x1984 chunk5x2000)))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x0 : span (checked 6) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x16 : span (checked 6) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x32 : span (checked 6) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x48 : span (checked 6) 16 48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x64 : span (checked 6) 16 64 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x80 : span (checked 6) 16 80 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x96 : span (checked 6) 16 96 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x112 : span (checked 6) 16 112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x128 : span (checked 6) 16 128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x144 : span (checked 6) 16 144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x160 : span (checked 6) 16 160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x176 : span (checked 6) 16 176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x192 : span (checked 6) 16 192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x208 : span (checked 6) 16 208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x224 : span (checked 6) 16 224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x240 : span (checked 6) 16 240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x256 : span (checked 6) 16 256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x272 : span (checked 6) 16 272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x288 : span (checked 6) 16 288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x304 : span (checked 6) 16 304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x320 : span (checked 6) 16 320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x336 : span (checked 6) 16 336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x352 : span (checked 6) 16 352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x368 : span (checked 6) 16 368 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x384 : span (checked 6) 16 384 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x400 : span (checked 6) 16 400 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x416 : span (checked 6) 16 416 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x432 : span (checked 6) 16 432 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x448 : span (checked 6) 16 448 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x464 : span (checked 6) 16 464 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x480 : span (checked 6) 16 480 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x496 : span (checked 6) 16 496 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x512 : span (checked 6) 16 512 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x528 : span (checked 6) 16 528 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x544 : span (checked 6) 16 544 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x560 : span (checked 6) 16 560 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x576 : span (checked 6) 16 576 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x592 : span (checked 6) 16 592 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x608 : span (checked 6) 16 608 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x624 : span (checked 6) 16 624 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x640 : span (checked 6) 16 640 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x656 : span (checked 6) 16 656 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x672 : span (checked 6) 16 672 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x688 : span (checked 6) 16 688 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x704 : span (checked 6) 16 704 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x720 : span (checked 6) 16 720 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x736 : span (checked 6) 16 736 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x752 : span (checked 6) 16 752 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x768 : span (checked 6) 16 768 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x784 : span (checked 6) 16 784 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x800 : span (checked 6) 16 800 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x816 : span (checked 6) 16 816 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x832 : span (checked 6) 16 832 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x848 : span (checked 6) 16 848 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x864 : span (checked 6) 16 864 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x880 : span (checked 6) 16 880 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x896 : span (checked 6) 16 896 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x912 : span (checked 6) 16 912 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x928 : span (checked 6) 16 928 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x944 : span (checked 6) 16 944 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x960 : span (checked 6) 16 960 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x976 : span (checked 6) 16 976 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x992 : span (checked 6) 16 992 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1008 : span (checked 6) 16 1008 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1024 : span (checked 6) 16 1024 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1040 : span (checked 6) 16 1040 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1056 : span (checked 6) 16 1056 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1072 : span (checked 6) 16 1072 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1088 : span (checked 6) 16 1088 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1104 : span (checked 6) 16 1104 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1120 : span (checked 6) 16 1120 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1136 : span (checked 6) 16 1136 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1152 : span (checked 6) 16 1152 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1168 : span (checked 6) 16 1168 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1184 : span (checked 6) 16 1184 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1200 : span (checked 6) 16 1200 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1216 : span (checked 6) 16 1216 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1232 : span (checked 6) 16 1232 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1248 : span (checked 6) 16 1248 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1264 : span (checked 6) 16 1264 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1280 : span (checked 6) 16 1280 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1296 : span (checked 6) 16 1296 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1312 : span (checked 6) 16 1312 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1328 : span (checked 6) 16 1328 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1344 : span (checked 6) 16 1344 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1360 : span (checked 6) 16 1360 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1376 : span (checked 6) 16 1376 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1392 : span (checked 6) 16 1392 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1408 : span (checked 6) 16 1408 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1424 : span (checked 6) 16 1424 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1440 : span (checked 6) 16 1440 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1456 : span (checked 6) 16 1456 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1472 : span (checked 6) 16 1472 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1488 : span (checked 6) 16 1488 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1504 : span (checked 6) 16 1504 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1520 : span (checked 6) 16 1520 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1536 : span (checked 6) 16 1536 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1552 : span (checked 6) 16 1552 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1568 : span (checked 6) 16 1568 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1584 : span (checked 6) 16 1584 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1600 : span (checked 6) 16 1600 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1616 : span (checked 6) 16 1616 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1632 : span (checked 6) 16 1632 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1648 : span (checked 6) 16 1648 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1664 : span (checked 6) 16 1664 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1680 : span (checked 6) 16 1680 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1696 : span (checked 6) 16 1696 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1712 : span (checked 6) 16 1712 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1728 : span (checked 6) 16 1728 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1744 : span (checked 6) 16 1744 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1760 : span (checked 6) 16 1760 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1776 : span (checked 6) 16 1776 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1792 : span (checked 6) 16 1792 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1808 : span (checked 6) 16 1808 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1824 : span (checked 6) 16 1824 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1840 : span (checked 6) 16 1840 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1856 : span (checked 6) 16 1856 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1872 : span (checked 6) 16 1872 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1888 : span (checked 6) 16 1888 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1904 : span (checked 6) 16 1904 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1920 : span (checked 6) 16 1920 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1936 : span (checked 6) 16 1936 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1952 : span (checked 6) 16 1952 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1968 : span (checked 6) 16 1968 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x1984 : span (checked 6) 16 1984 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2000 : span (checked 6) 16 2000 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2016 : span (checked 6) 16 2016 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2032 : span (checked 6) 16 2032 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2048 : span (checked 6) 16 2048 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2064 : span (checked 6) 16 2064 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2080 : span (checked 6) 16 2080 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2096 : span (checked 6) 16 2096 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2112 : span (checked 6) 16 2112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2128 : span (checked 6) 16 2128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2144 : span (checked 6) 16 2144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2160 : span (checked 6) 16 2160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2176 : span (checked 6) 16 2176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2192 : span (checked 6) 16 2192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2208 : span (checked 6) 16 2208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2224 : span (checked 6) 16 2224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2240 : span (checked 6) 16 2240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2256 : span (checked 6) 16 2256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2272 : span (checked 6) 16 2272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2288 : span (checked 6) 16 2288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2304 : span (checked 6) 16 2304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2320 : span (checked 6) 16 2320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2336 : span (checked 6) 16 2336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2352 : span (checked 6) 16 2352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2368 : span (checked 6) 16 2368 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2384 : span (checked 6) 16 2384 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2400 : span (checked 6) 16 2400 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2416 : span (checked 6) 16 2416 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2432 : span (checked 6) 16 2432 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2448 : span (checked 6) 16 2448 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2464 : span (checked 6) 16 2464 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2480 : span (checked 6) 16 2480 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2496 : span (checked 6) 16 2496 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk6x2512 : span (checked 6) 8 2512 = true := by decide +kernel

theorem layer6 : span (checked 6) 2520 0 = true :=
  (@span_join (checked 6) 1264 0 1256 (@span_join (checked 6) 624 0 640 (@span_join (checked 6) 304 0 320 (@span_join (checked 6) 144 0 160 (@span_join (checked 6) 64 0 80 (@span_join (checked 6) 32 0 32 (@span_join (checked 6) 16 0 16 chunk6x0 chunk6x16) (@span_join (checked 6) 16 32 16 chunk6x32 chunk6x48)) (@span_join (checked 6) 32 64 48 (@span_join (checked 6) 16 64 16 chunk6x64 chunk6x80) (@span_join (checked 6) 16 96 32 chunk6x96 (@span_join (checked 6) 16 112 16 chunk6x112 chunk6x128)))) (@span_join (checked 6) 80 144 80 (@span_join (checked 6) 32 144 48 (@span_join (checked 6) 16 144 16 chunk6x144 chunk6x160) (@span_join (checked 6) 16 176 32 chunk6x176 (@span_join (checked 6) 16 192 16 chunk6x192 chunk6x208))) (@span_join (checked 6) 32 224 48 (@span_join (checked 6) 16 224 16 chunk6x224 chunk6x240) (@span_join (checked 6) 16 256 32 chunk6x256 (@span_join (checked 6) 16 272 16 chunk6x272 chunk6x288))))) (@span_join (checked 6) 160 304 160 (@span_join (checked 6) 80 304 80 (@span_join (checked 6) 32 304 48 (@span_join (checked 6) 16 304 16 chunk6x304 chunk6x320) (@span_join (checked 6) 16 336 32 chunk6x336 (@span_join (checked 6) 16 352 16 chunk6x352 chunk6x368))) (@span_join (checked 6) 32 384 48 (@span_join (checked 6) 16 384 16 chunk6x384 chunk6x400) (@span_join (checked 6) 16 416 32 chunk6x416 (@span_join (checked 6) 16 432 16 chunk6x432 chunk6x448)))) (@span_join (checked 6) 80 464 80 (@span_join (checked 6) 32 464 48 (@span_join (checked 6) 16 464 16 chunk6x464 chunk6x480) (@span_join (checked 6) 16 496 32 chunk6x496 (@span_join (checked 6) 16 512 16 chunk6x512 chunk6x528))) (@span_join (checked 6) 32 544 48 (@span_join (checked 6) 16 544 16 chunk6x544 chunk6x560) (@span_join (checked 6) 16 576 32 chunk6x576 (@span_join (checked 6) 16 592 16 chunk6x592 chunk6x608)))))) (@span_join (checked 6) 320 624 320 (@span_join (checked 6) 160 624 160 (@span_join (checked 6) 80 624 80 (@span_join (checked 6) 32 624 48 (@span_join (checked 6) 16 624 16 chunk6x624 chunk6x640) (@span_join (checked 6) 16 656 32 chunk6x656 (@span_join (checked 6) 16 672 16 chunk6x672 chunk6x688))) (@span_join (checked 6) 32 704 48 (@span_join (checked 6) 16 704 16 chunk6x704 chunk6x720) (@span_join (checked 6) 16 736 32 chunk6x736 (@span_join (checked 6) 16 752 16 chunk6x752 chunk6x768)))) (@span_join (checked 6) 80 784 80 (@span_join (checked 6) 32 784 48 (@span_join (checked 6) 16 784 16 chunk6x784 chunk6x800) (@span_join (checked 6) 16 816 32 chunk6x816 (@span_join (checked 6) 16 832 16 chunk6x832 chunk6x848))) (@span_join (checked 6) 32 864 48 (@span_join (checked 6) 16 864 16 chunk6x864 chunk6x880) (@span_join (checked 6) 16 896 32 chunk6x896 (@span_join (checked 6) 16 912 16 chunk6x912 chunk6x928))))) (@span_join (checked 6) 160 944 160 (@span_join (checked 6) 80 944 80 (@span_join (checked 6) 32 944 48 (@span_join (checked 6) 16 944 16 chunk6x944 chunk6x960) (@span_join (checked 6) 16 976 32 chunk6x976 (@span_join (checked 6) 16 992 16 chunk6x992 chunk6x1008))) (@span_join (checked 6) 32 1024 48 (@span_join (checked 6) 16 1024 16 chunk6x1024 chunk6x1040) (@span_join (checked 6) 16 1056 32 chunk6x1056 (@span_join (checked 6) 16 1072 16 chunk6x1072 chunk6x1088)))) (@span_join (checked 6) 80 1104 80 (@span_join (checked 6) 32 1104 48 (@span_join (checked 6) 16 1104 16 chunk6x1104 chunk6x1120) (@span_join (checked 6) 16 1136 32 chunk6x1136 (@span_join (checked 6) 16 1152 16 chunk6x1152 chunk6x1168))) (@span_join (checked 6) 32 1184 48 (@span_join (checked 6) 16 1184 16 chunk6x1184 chunk6x1200) (@span_join (checked 6) 16 1216 32 chunk6x1216 (@span_join (checked 6) 16 1232 16 chunk6x1232 chunk6x1248))))))) (@span_join (checked 6) 624 1264 632 (@span_join (checked 6) 304 1264 320 (@span_join (checked 6) 144 1264 160 (@span_join (checked 6) 64 1264 80 (@span_join (checked 6) 32 1264 32 (@span_join (checked 6) 16 1264 16 chunk6x1264 chunk6x1280) (@span_join (checked 6) 16 1296 16 chunk6x1296 chunk6x1312)) (@span_join (checked 6) 32 1328 48 (@span_join (checked 6) 16 1328 16 chunk6x1328 chunk6x1344) (@span_join (checked 6) 16 1360 32 chunk6x1360 (@span_join (checked 6) 16 1376 16 chunk6x1376 chunk6x1392)))) (@span_join (checked 6) 80 1408 80 (@span_join (checked 6) 32 1408 48 (@span_join (checked 6) 16 1408 16 chunk6x1408 chunk6x1424) (@span_join (checked 6) 16 1440 32 chunk6x1440 (@span_join (checked 6) 16 1456 16 chunk6x1456 chunk6x1472))) (@span_join (checked 6) 32 1488 48 (@span_join (checked 6) 16 1488 16 chunk6x1488 chunk6x1504) (@span_join (checked 6) 16 1520 32 chunk6x1520 (@span_join (checked 6) 16 1536 16 chunk6x1536 chunk6x1552))))) (@span_join (checked 6) 160 1568 160 (@span_join (checked 6) 80 1568 80 (@span_join (checked 6) 32 1568 48 (@span_join (checked 6) 16 1568 16 chunk6x1568 chunk6x1584) (@span_join (checked 6) 16 1600 32 chunk6x1600 (@span_join (checked 6) 16 1616 16 chunk6x1616 chunk6x1632))) (@span_join (checked 6) 32 1648 48 (@span_join (checked 6) 16 1648 16 chunk6x1648 chunk6x1664) (@span_join (checked 6) 16 1680 32 chunk6x1680 (@span_join (checked 6) 16 1696 16 chunk6x1696 chunk6x1712)))) (@span_join (checked 6) 80 1728 80 (@span_join (checked 6) 32 1728 48 (@span_join (checked 6) 16 1728 16 chunk6x1728 chunk6x1744) (@span_join (checked 6) 16 1760 32 chunk6x1760 (@span_join (checked 6) 16 1776 16 chunk6x1776 chunk6x1792))) (@span_join (checked 6) 32 1808 48 (@span_join (checked 6) 16 1808 16 chunk6x1808 chunk6x1824) (@span_join (checked 6) 16 1840 32 chunk6x1840 (@span_join (checked 6) 16 1856 16 chunk6x1856 chunk6x1872)))))) (@span_join (checked 6) 320 1888 312 (@span_join (checked 6) 160 1888 160 (@span_join (checked 6) 80 1888 80 (@span_join (checked 6) 32 1888 48 (@span_join (checked 6) 16 1888 16 chunk6x1888 chunk6x1904) (@span_join (checked 6) 16 1920 32 chunk6x1920 (@span_join (checked 6) 16 1936 16 chunk6x1936 chunk6x1952))) (@span_join (checked 6) 32 1968 48 (@span_join (checked 6) 16 1968 16 chunk6x1968 chunk6x1984) (@span_join (checked 6) 16 2000 32 chunk6x2000 (@span_join (checked 6) 16 2016 16 chunk6x2016 chunk6x2032)))) (@span_join (checked 6) 80 2048 80 (@span_join (checked 6) 32 2048 48 (@span_join (checked 6) 16 2048 16 chunk6x2048 chunk6x2064) (@span_join (checked 6) 16 2080 32 chunk6x2080 (@span_join (checked 6) 16 2096 16 chunk6x2096 chunk6x2112))) (@span_join (checked 6) 32 2128 48 (@span_join (checked 6) 16 2128 16 chunk6x2128 chunk6x2144) (@span_join (checked 6) 16 2160 32 chunk6x2160 (@span_join (checked 6) 16 2176 16 chunk6x2176 chunk6x2192))))) (@span_join (checked 6) 160 2208 152 (@span_join (checked 6) 80 2208 80 (@span_join (checked 6) 32 2208 48 (@span_join (checked 6) 16 2208 16 chunk6x2208 chunk6x2224) (@span_join (checked 6) 16 2240 32 chunk6x2240 (@span_join (checked 6) 16 2256 16 chunk6x2256 chunk6x2272))) (@span_join (checked 6) 32 2288 48 (@span_join (checked 6) 16 2288 16 chunk6x2288 chunk6x2304) (@span_join (checked 6) 16 2320 32 chunk6x2320 (@span_join (checked 6) 16 2336 16 chunk6x2336 chunk6x2352)))) (@span_join (checked 6) 80 2368 72 (@span_join (checked 6) 32 2368 48 (@span_join (checked 6) 16 2368 16 chunk6x2368 chunk6x2384) (@span_join (checked 6) 16 2400 32 chunk6x2400 (@span_join (checked 6) 16 2416 16 chunk6x2416 chunk6x2432))) (@span_join (checked 6) 32 2448 40 (@span_join (checked 6) 16 2448 16 chunk6x2448 chunk6x2464) (@span_join (checked 6) 16 2480 24 chunk6x2480 (@span_join (checked 6) 16 2496 8 chunk6x2496 chunk6x2512))))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x0 : span (checked 7) 16 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x16 : span (checked 7) 16 16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x32 : span (checked 7) 16 32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x48 : span (checked 7) 16 48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x64 : span (checked 7) 16 64 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x80 : span (checked 7) 16 80 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x96 : span (checked 7) 16 96 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x112 : span (checked 7) 16 112 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x128 : span (checked 7) 16 128 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x144 : span (checked 7) 16 144 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x160 : span (checked 7) 16 160 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x176 : span (checked 7) 16 176 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x192 : span (checked 7) 16 192 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x208 : span (checked 7) 16 208 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x224 : span (checked 7) 16 224 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x240 : span (checked 7) 16 240 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x256 : span (checked 7) 16 256 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x272 : span (checked 7) 16 272 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x288 : span (checked 7) 16 288 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x304 : span (checked 7) 16 304 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x320 : span (checked 7) 16 320 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x336 : span (checked 7) 16 336 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x352 : span (checked 7) 16 352 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk7x368 : span (checked 7) 16 368 = true := by decide +kernel

theorem layer7 : span (checked 7) 384 0 = true :=
  (@span_join (checked 7) 192 0 192 (@span_join (checked 7) 96 0 96 (@span_join (checked 7) 48 0 48 (@span_join (checked 7) 16 0 32 chunk7x0 (@span_join (checked 7) 16 16 16 chunk7x16 chunk7x32)) (@span_join (checked 7) 16 48 32 chunk7x48 (@span_join (checked 7) 16 64 16 chunk7x64 chunk7x80))) (@span_join (checked 7) 48 96 48 (@span_join (checked 7) 16 96 32 chunk7x96 (@span_join (checked 7) 16 112 16 chunk7x112 chunk7x128)) (@span_join (checked 7) 16 144 32 chunk7x144 (@span_join (checked 7) 16 160 16 chunk7x160 chunk7x176)))) (@span_join (checked 7) 96 192 96 (@span_join (checked 7) 48 192 48 (@span_join (checked 7) 16 192 32 chunk7x192 (@span_join (checked 7) 16 208 16 chunk7x208 chunk7x224)) (@span_join (checked 7) 16 240 32 chunk7x240 (@span_join (checked 7) 16 256 16 chunk7x256 chunk7x272))) (@span_join (checked 7) 48 288 48 (@span_join (checked 7) 16 288 32 chunk7x288 (@span_join (checked 7) 16 304 16 chunk7x304 chunk7x320)) (@span_join (checked 7) 16 336 32 chunk7x336 (@span_join (checked 7) 16 352 16 chunk7x352 chunk7x368)))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk8x0 : span (checked 8) 9 0 = true := by decide +kernel

theorem layer8 : span (checked 8) 9 0 = true :=
  chunk8x0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk9x0 : span (checked 9) 1 0 = true := by decide +kernel

theorem layer9 : span (checked 9) 1 0 = true :=
  chunk9x0

theorem verified : ∀ k ≤ 9, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer9 i (Nat.zero_le i) (by simpa [counts] using hi)

theorem prismLower (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : canonical (evaluate p Prism.initial o) = Prism.target) : 10 ≤ p.length :=
  lower_from_checks verified p o hit

end PrismSignedFrontier.Certificate
