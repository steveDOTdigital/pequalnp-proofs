import PrismFastClosure

namespace PrismSignedFrontier.SmallCert

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

end PrismSignedFrontier.SmallCert

namespace PrismSignedFrontier.SmallCert.Friend

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]
def target : W := 0xfffef888fffef888
def negative : List Nat := [0, 1, 2, 4, 5, 6, 8, 9, 10, 16]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨8,12,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨4,12,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,17,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 3 then (if page < 1 then 0xa0a0a0a0a0a0a0a0a0a00000a0a000008aaa8aaa8aaa8aaa88cc88cc88cc88cc88aaaaaa88aaaaaa88aa88aa88aa88aa88aa888888aa8888888a888a888a888a8888aaaa8888aaaa8888888888888888888800008888000080808080808080805555000055550000550055005500550044444444444444443fff00003fff000033ff000033ff000033cc33cc33cc33cc2aaa2aaa2aaa2aaa22aaaaaa22aaaaaa22aa22aa22aa22aa22222222222222220fff00000fff00000ff00ff00ff00ff00f0f00000f0f00000f000f000f000f000ccc0ccc0ccc0ccc0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a08aa08aa08aa08aa00ffff0000ffff0000ff00fa00ff00fa00ff00f000ff00f000ff00aa00ff00aa00ff000000ff000000fa00fa00fa00fa00f300f000f300f000f0f0f000f0f0f000f000f000f000f000f0000000f0000000ee00ee00ee00ee00cccccc00cccccc00aaaaaa00aaaaaa00aa88aa00aa88aa00aa0aaa00aa0aaa00aa00aa00aa00aa00aa000000aa000000a000a000a000a0008800880088008800330000003300000022aaaa0022aaaa0022002200220022000f0000000f0000000aaaaa000aaaaa000a000a000a000a0000fafa0000fafa0000eeee0000eeee0000aaaa0000aaaa0000a0a00000a0a00000888800008888000000f0000000f0000000aa000000aa0000000000000000 else (if page < 2 then 0xff0aff00ff0aff00ff08ff08ff08ff08ff02ff02ff02ff02ff00ff88ff00ff88ff00ff0aff00ff0aff00ff00ff00ff00ff00f000ff00f000ff000000ff000000fefefefefefefefefcfcfcfcfcfcfcfcfcfcf8f8fcfcf8f8fcccfcccfcccfcccfafafafafafafafafafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000f8faf8faf8faf8faf8f8f8f8f8f8f8f8f3f0f3f0f3f0f3f0f300f300f300f300f0faf0faf0faf0faf0f0f0f0f0f0f0f0f0f0f000f0f0f000f050f050f050f050f000f000f000f000eeeeeeeeeeeeeeeeeeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eaeaeaeaeaeaeaeadddcdddcdddcdddcddccddccddccddccdcdcdcdcdcdcdcdccccccccccccccccccccc8888cccc8888bbbbaaaabbbbaaaabbbb8888bbbb8888bbbb0000bbbb0000babababababababaafff0000afff0000aaffaaaaaaffaaaaaaff0000aaff0000aafaaafaaafaaafaaaeeaaeeaaeeaaeeaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaaa8a8aaaaa8a8aaaaa0a0aaaaa0a0aaaa88aaaaaa88aaaaaa8888aaaa8888aaaa2222aaaa2222aaaa0aaaaaaa0aaaaaaa00aaaaaa00aaaaaa0000aaaa0000aaa0aaa0aaa0aaa0aa00aa00aa00aa00a8aaa8aaa8aaa8aaa8a8a8a8a8a8a8a8a0f0f0f0a0f0f0f0a0f0a0f0a0f0a0f0a0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0aaaaa0a0aaaa else 0xffffff00ffffff00fffffafafffffafafffff0f0fffff0f0fffff000fffff000ffffeeeeffffeeeeffffccccffffccccffffaaaaffffaaaaffffa0a0ffffa0a0ffff8888ffff8888ffff8080ffff8080ffff00f0ffff00f0ffff00aaffff00aaffff0088ffff0088ffff0000ffff0000fffcfcccfffcfcccfffafffafffafffafffaff00fffaff00fff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0fff0f000fff0f000fff000f0fff000f0ffeeff00ffeeff00ffccffccffccffccffccff88ffccff88ffccff00ffccff00ffccfcccffccfcccffccccccffccccccffaaffaaffaaffaaffaaff88ffaaff88ffaaff0affaaff0affaaff00ffaaff00ffa0ff00ffa0ff00ff8aff8aff8aff8aff88ff88ff88ff88ff88ff00ff88ff00ff80ff80ff80ff80ff30ff00ff30ff00ff22ff00ff22ff00ff0ff000ff0ff000ff0eff0eff0eff0eff0cff0cff0cff0cff0aff0aff0aff0a)) else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xa79c51a76151 else 0
  | 3 => if page < 1 then 0x9d9275519d916a4d9d816a4d835e511c9d946a369d826a36a78f6a519d965e51a7906a51a7975e51a7937651a77a5f51a76d5e51a75e510aa7965e51a79b5e51a27a6a16a79974519d886e669d938e6ea7995e23a7995e51 else 0
  | 4 => if page < 3 then (if page < 1 then 0x9d7a6a5e429d806a5e519d7d6a5e519d7a6a5e46675e51271c9d7a6a5b519d916a51369d7a6a64369d938e6a369d816a51369d7a6a54369d6a5e51289d675e510a9d7a6a63369d7a776a369d7a6a36169d995e51289d675e51289d7a6a5e4da27a6a5e49a79d995e51a27a6a6636a76a5e511ca27a6a5e4da78e6a5e51a27a6a5e11a7996a5e5100a7995e5199675e51299d7a6a6603a27a6a5e519d7c6a5e519d7a6a5e4b7a6a5e51299d876a5e519d7a6a5e249d7a5e51199d886a6636a2886a5e517a746a51299d886e5e519d8e746a519d7a6e5e119d7a6a5e3a9d99675e23a77a6a5e237a6a5e29239d7a746a239d7a6a25239d8e6a5e239d7a685e239e7a6a5e517a6a5e58519d886a5e519d7e6a5e519d7a6a5e3da17a6a5e517a6a5e51309d866a5e519d7a6a5e2d9d7a6a5e23a77a5e51189d7a6a66369d7a6a5e51 else (if page < 2 then 0x796a5e511c9d695e511c9d6a5e511a9d7a6a5e399d8c6a5e519d7a6a5e139d7a6a5d499d6a5e51207a6a5e51209d8b725e51aa9d8f6a519d8f7a6a149d7a6a15149d8b6a65519d977a5e14aa9d975e51a8986a5e51977a5e511c9d7a6a654d9d8f7a51199d7a5e19149d8b6a5e059d7a6a65059d6a5e511f9d7a6a5e509d9a6a5e519d7a6a5e0c9d7a766a4d9d7a6a5d119d7b6a5e519d7a6a5e4e9d8b6a5e519d7f6a5e519d7a6a5e3b9d856a5e519d7a5e5144a89d7a5f519d806a5e059d896a5e519d7a6a5e219d937a6a3a9d7a6a3c119d8e6a5e3a9d7a6f5e3a9d6c6a5e219d6a5e512e9d8a6a5e519d7a6a5e2c9d7a6a5e149d946a5e519d7a6a5e099d826a5e519d7a6a5e389d7a6a664daaa8995e519d975e51189d8f6a51189d956a5e519d795e5118a85e511c189d6a6051189d6a5e511e9d986a5e519d846a5e51 else 0x9d8d6a5e519d7a6a5e129d8d6a5e4d9d796a5e12)) else 0
  | 5 => if page < 3 then (if page < 1 then 0x9d7a6a5e54519d7a6a5e51439d7a6a5e513f9d7a735e513fa39d7a6a5e519d7a6a5e512f9d7a6a5e51049d7a6a5e513e9d7a6a625e519d7a6a5e512b9d7a6a5e51119d7a6a5e4711a69d7a6a5e519d7a6a5e510a9d7a6a5e51069d7a6a635e519d7a776a5e519d7a6a5e51089d7a6a5e51169d7a6a5e5148aa9d996a5e519d7a6a665e059d6a5e511c189d786a5e5118a89d7a5e51189d7a6a5e2a059d6a5e5126189d8e6a5e51189d7a6a5e3111a09d7a6a5e519d7a6a5e5a519d7a6a5e51029d7a6a5e51179d7a6a665e519d996a5e51189d7a6a5e51369d7a6a5e55519d7a6a5e51419d7a6a5e510b9d7a6a5e510f9d6a675e511c9d7a6a5e49369d7a766a51369d7a6a5e36119d7a6a665136009d7a6a6636a29d7a6a5e51a27a6a5e513600a27a6a5e519d7a6a5e51297a6a675e5129007a6a5e51299d7a6a5e51039d7a6a5e51359d7a6e6a5e519d886a5e5136009d886a5e519d7a6a5e51239d7a6a675e23009d7a6a5e239d7a6a5e510e9d7a6a5e51349d7a6a5e51189d7a675e5118 else (if page < 2 then 0xa59d7a6a5e4d9d7a6a5e514d009d7a6a5e4da5a47a6a5e51a87a6a5e511c7a6a5e51271caa9d6a5e511c9d7a6a5e5c519d7a6a5e51379d7a6a5e57519d7a6a5e51409d7a6a5e33057a6a5e513305a49d7a6a5e51a47a6a5e51059d7a6a5e53519d7a6a5e514a9d7a6a5e52519d7a6a5e514c9d7a6a5e5149a49d7a6a5e49a47a6a5e51499d7a6a5e511c7a786a5e511c9d7a716a5e519d8b6a5e5149009d8b6a5e519d7a6a5e51149d7a786a5e14009d7a6a5e149d7a6a645e519d7a6a655149009d986a5e519d7a6a5e51199d7a785e5119009d7a5e51199d7a6a5e51059d7a6a5e4905a99d7a6a5e519d7a6a5e510d9d7a6a5e51079d7a706a5e519d7a6a5e511b9d7a6a5e5145aa9d8e6a5e519d7a736a5e059d938e6a5e51a49d7a6a5e119d7a6a5e11059d6a5e5132119d7a736a5e119d7a6a5e22119f9d7a6a5e519d7a6a5e56519d7a6a5e51019d7a6a5e51109d7a736a5e519d8e6a5e51119d7a6a5e59519d7a6b5e5111009d806a5e519d7a6a5e513a9d7a685e5111009d7a6a5e3a else 0x9d7a6a5e511d9d7a6a5e514fa89d6a5e511e9d7a6a5e511e009d6a5e511e)) else 0
  | 6 => if page < 1 then 0xa49d7a6a5e51009d7a6a5e511c009d7a6a5e5105009d7a6a5e5149009d7a736a5e51009d7a6a5e5111009d7a6a5e513f009d7a6a665e51009d7a6a5e5118009d7a6a5e5136 else 0
  | 7 => if page < 1 then 0x9d7a6a5e51 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 2
  | 3 => 22
  | 4 => 132
  | 5 => 133
  | 6 => 10
  | 7 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 256
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 8)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (8*(k+1)) i)

def entries : ℕ → ℕ
  | 2 => 4
  | 3 => 46
  | 4 => 254
  | 5 => 235
  | 6 => 40
  | 7 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xe1d304b2c6e524e0b8fac8bb5a60bce6 else 0
  | 3 => if page < 1 then 0xfeb73b69f685fe11f3e087f7f2984700f0d14f83e8c81c91e81887fadfcee029cef5eb32c8c6109fc285bbbdc20a97efb4d13e10ac3832c3ab5882d0a49d0a20a262c8308d7c54c18b3c64d182b1831574c33dbe71ee135960d97dc55a8d8c685630819153c510a453b3a2cf4c725728436beff6431c6a393b42a1bf38ddfac43508c52630f95e322e5ff3e42ad92042239b2db31d78caae1c12eac31afb13731acbe86d1ab539561a616e620ba9054309076e8106ae26c3 else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x3bd20da53b004ef93aecb73c380567ea36e3389c34f5957833081aaa32a12130312cd94130d7d7702fde08122f381a662ec11fa22ebc05a52cf644a12cad27122b3412b0293b83d32748d35a233fca9d232a7c93206642c51fb5ffaf1f81169d1f01210a1e62e4f71ddbfb2c1da5d5341d8fd48a1bbc5ff51a1133dc19390ced18fa86ff17b09d0216895a231639080f162aedae16007c4414c7c75a1320650012ac438910d2c37f0fc901020f6d795e0f1678820ec9b8780e1f657a0db7c1bb0d4dcb220d3c95ba0aaedb9c0a1511ca09cdea0208bce33b085dc47a07e464700609230705a0f35705721cc50385ca24036dc77901ea673a01a1b8d1014c7482 else 0x7b0ba3a279558c7e794dce6e78ffbe8d78480ee2775c07d876b64b5274e621bd74230e0373e6a9b27344731d72ee57e9727bcd26725a56186ffad2a26f0f4a016efabe336e7ee54c6e68b2596d9ac57b6d4a7f5a6b85eb226b41db6e68689eeb67e5eca4679ec0bf66f5c3df66d907ee663359d264bbeb83649ad3e76225f81c60de34e960a7e8bc5ffaad225fadf55b5f057d695ef09b6c5ece992a5dfb62895d0bc9da5c0bfa3258dd8211584cc025582ceec056d0d2cf569a2d53567ec97255a30f47545942d1534a30895104b4d94e9c9b814df2fd534c1b47ad4c18d8ed4932766a48efcf5f48d4eee0484d90394699ecbe3ecb82b83d64450b3c862bc7) else (if page < 3 then 0xd0132035d00062ceceeb0947ccf5b0a6cc7efde3c9834d3ec902e126c816e245c5e1f01cc42cf630c3475c74c32859a6c0cfd407c0b024f7bf273ce9bbcd24d3b7c96cd5b5fc4931b30d5a0eb2b7a267b00b5950aed0cc5bae142952adcfc0d5ad555bd0ad3b77a3acefc7e5ac7d9c9ba8ac71d1a6472779a63a2b0fa556db11a3a032f5a2b92f9ba26b85c79fbeff949f369d219a0948a898d529b491a3063790e9f022907067a28fef3b518d48b64f8cb2c2378b405bd78b388448894c7cd088d999aa8852c875880114aa87bf8f2887a2b3b08760c898864f77d1863b957a8585872f844147b3800682227f93ff217e1780887d683af17c349cf97c3003fa else 0xffb50448ff99e1b0fe8af3b7fe571042fe4a9e1dfcfecbc0fc6ebabefa4303a8fa30bdaef9ef91f8f8e47014f86fbfaff837faa5f7dbce2bf7b26fd2f7ac7181f7262c3ef4a70378f38f6f6ff2984700f08362bdefdac1b7ee46e0efedd5dbdeed301194ebdbe0ffeb5d587beaa53022ea21c21fe9759daee9410aefe91e8333e88731d0e7d417c8e78a8aa2e6f30f7ee6f0db0de64b9038e2a3c148e2940b81e2337144e0a94a90e0566a0fdffc69addf502174ded67679de6dd8e5dd992d01dd07de53dcf50326dbcc377fda03845ad9ddeb3fd6ccac29d5d70b81d4f46969d44b2c57d3707df0d334b7d2d2fd3f87d284a609d0b32cf4)) else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0x3a5dbe7739e7bc0939e7906d3910fe5a38c2e72138bd42093792eefa3785d685373ab3ad34a5234b33081aaa32fc894132b9aada31b3fc4131af99242f8765002d0aac292c7d5a0c2b5875a42b34d4252ac67a832a59c6102a4e63ee2a4b240c2a15c4de29dc884e29afe2412748d35a23a36f892098e5341faede2b1ecb13701e62e4f71e07b2b21db1afc21d84f2fc1bbc5ff51a1133dc17f01a6217140bae16c902a616aa0bd815d91bfb1414b663139e5aed12bd13e312a7b511126f927912228d5c11c055250f03c24f0db7c1bb0c361b650b023bf708bce33b08b8fb6a07ef6f5f0537bb520436b133040f5e7403cbaf95036dbf7c0274ce2500fedace else 0x79cd6329799d62e177c193f777915bec75bfbe45747d47e572e44a886da288956d9372056c1200f9683f3dbf66f5c3df663359d2662f794964e0df9c64ca1ad164ad83a2649ad3e764477e9662ad91376206fea0604fd1515efd7d3b5ec24cc05df782005d759b135c4219835b9897625b508c5d5b26faf75acf6b6f5a4230ec58962500586289f656f1886056964cca5590c9d55582a04f547120805437622c541bbbff53ad9e5352bb74d651f6a9e0505079bf4f5212944ed7d3014e22b5d04d60434f4932766a473c402b46a5a76a4417b97b4295b5c0425ace1340a027d33f4472343f36ebd23f17b1d23ea44c4a3dc884de3bca648b3af1a2233aecb73c) else (if page < 3 then 0xc32ba1c3c2819d59c170abccc11b7986bdadb56cbb167defbab196bfba67e384b8d46160b6d2e41bb5a7ed8fb2ea4cbeb2980285b20f1f2cac7df87dac022995abf9f006aaade9f6a931fca0a7d12d97a6c48379a60c610ca467b237a3ce0d26a365dc0aa21a8cd09e47ac0b9e1f4ea79daaabf79c424af69ba50b4b9aac0f9e9814d8219745994e95f31d7695e7575e94e115c0942b69b99365286a9239780b920a7820915b6e5090665f509035f9e68f7d15158e8c228b8e8622288deec1e78afe316e893abf0f88f4bfb5873e4071868901bb864f77d18553dc7684267de1819a12997f93ff217d4d26bb7c41e14f7c0a617a7ad6cde279fe703679ea6904 else 0xff960127fde85718fd371689fcbd8d07fad2ef23fa1b5d40f5151788f231f492eebd8a54ed5d3b6ce9d2420ee8442691e7dd780ae781bc84e6f0db0de5e93699e5229618dc4ebedfdbfc3d9edb8405e9db175718da95c8e8da70d062d92cbe4bd62f6babd60a2cc4d498bdebd4582a01d44b2c57d438ef2bd34e184bd3088ba8cffaf049cee109e7ce6cbb82ce336b0ccc9a167ccc84ecf8cbfcc9c6ca80d91cc9834d3ec7bd5d2ac42b78e5)) else 0
  | 6 => if page < 1 then 0xf2fc17e3e88e58e8e87ae12bdc65205cdc4ebedfca4e1418bb167defba471675b9aeaea6b2130c43a0e52aa09e1f4ea79cf57ba99c424af69a8736c19814d82194e115c09365286a8d800da782169a357ee7b70a7d4d26bb752a5c7a6b0d2e9b662f794963d08eab626e621d58cbc3b84edd9eb34295b5c03ea44c4a3de0ca1d3af1a22339e7906d3536dd5a2571d7791bca8c1e18f3e8b00f03c24f017826f7 else 0
  | 7 => if page < 1 then 0xf4a70378 else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x4000500220020 else 0
  | 3 => if page < 1 then 0x241022000000004004601c0022100c2016202830126026300e0024001e7014500600040018602a2014600c4028200a0020001a601e4018401e600a602010085026500840284012400a401a7016400c0024601c40100002400200025 else 0
  | 4 => if page < 4 then (if page < 2 then (if page < 1 then 0x54008460141028006a2102101400fa405a00e600aa601a00a0310600be102a10f610ce509e60ca309810a80072302c400850c0004c30c800ee609e702860a2006c30745100609a50ea6060106600b0603040a43032107e102200d4003a1006408e6058203640940006000650fe60320050004e50dc009240260064001c106c2 else 0x26500c502e0052404000b650d410f220ae004a605c40d86028706e10b4105a50d600867090006210c810d001020066407c004e70020038508240cc4084404400104056405800b640ac2052609a40e060c070f8206800b400c6208660d200a66088009010d800e8608a603e401a5020403660e0102c608e0046401800dc60c41) else (if page < 3 then 0x1c009c10600012103e504200b870cc008060744052004c10700042409e10502072204e40c2602820ec00a2408a00c840e800341104708040de00c600bc6034000e00da004a40de406a007a10e260dc10ca706e00e400e2703a00fe00044082004c00a0708c00c0601a102a30c010ac70c6305e4026407c10ea70f200ce20da4 else 0x40070208c604010aa007e3030202a001c403c00826106107600e4102000384014600000460048404c201e0002407860d8200a00f4609200fc01007082109040944030005a4004605a206200d24024408e20fc40ae6022204e609e009c002450b210d040f06104606840d620240096403c40e2008400ba40a420165)) else 0
  | 5 => if page < 4 then (if page < 2 then (if page < 1 then 0xa6703430d26016009600406022002810482092000e00a410d6005420f2606c309a403600b400d00032402a00e8007c708c0050609000c4609470440046507e20ca00300108001a40c4708060dc2058502600b21006009270a44020004a003620d0606200d850084104407430085012007010ee40ec005200a85090103a00061 else 0x56409a00e85066003260d4006e504670c660e600fc202400be40024028205c00cc0100405c50b000c6709020f640e0504e409800ac00a000006014004c40a2106860a2600a404c00de705e108c609e00ce402a2046000a5064403410da20aa408a40b860b200566030408e101c407200540070003a406a603a60ae00d8000e1) else (if page < 3 then 0xaa005c4004104e002e0038401210040040405a0072102a503270a660c0006e203e40a40048609c70ec20ce505e406400c8707600f6006a10e040e4006800f200e450b0208c10a010b6005000026028310640e6500c50ea30ba60fe209e100440320082009260f4010810ca10481010102c2086103c401000b030de602a10a61 else 0x405a1028003e0032300000c860784088002e40600026208460c220fa21024106507a102a300c40ea105840f8004250a8206810f0402c00184078002e6040009c009210e2005e00cc104a103020bc601e0048006c7)) else 0
  | 6 => if page < 1 then 0x6300c40087006000610083000400a000c200a301220081008201200085012500e00026002101240100004400e501010024008000a200e2004000a10086000000c001060084010400e4006200c50020 else 0
  | 7 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def search (k h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if field keys k 32 m ≤ h then search k h fuel m hi else search k h fuel lo m
    else lo

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let ix := search k (key xs) 14 0 (entries k)
  let slot := field targets k 16 ix
  (slot / 32,slot % 32)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s01]
  | 3 => [s01, s23]
  | 4 => [s02, s13]
  | 5 => [s02, s13, s01]
  | 6 => [s03, s12, s01]
  | 7 => [s03, s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s01_ok, s02_ok, s13_ok, s03_ok, s12_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 7 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 2 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 2 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x16 : span (checked 3) 6 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 22 0 = true :=
  (@span_join (checked 3) 16 0 6 chunk3x0 chunk3x16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x16 : span (checked 4) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x32 : span (checked 4) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x48 : span (checked 4) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x64 : span (checked 4) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x80 : span (checked 4) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x96 : span (checked 4) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x112 : span (checked 4) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x128 : span (checked 4) 4 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 132 0 = true :=
  (@span_join (checked 4) 64 0 68 (@span_join (checked 4) 32 0 32 (@span_join (checked 4) 16 0 16 chunk4x0 chunk4x16) (@span_join (checked 4) 16 32 16 chunk4x32 chunk4x48)) (@span_join (checked 4) 32 64 36 (@span_join (checked 4) 16 64 16 chunk4x64 chunk4x80) (@span_join (checked 4) 16 96 20 chunk4x96 (@span_join (checked 4) 16 112 4 chunk4x112 chunk4x128))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x16 : span (checked 5) 16 16 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x32 : span (checked 5) 16 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x48 : span (checked 5) 16 48 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x64 : span (checked 5) 16 64 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x80 : span (checked 5) 16 80 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x96 : span (checked 5) 16 96 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x112 : span (checked 5) 16 112 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x128 : span (checked 5) 5 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 133 0 = true :=
  (@span_join (checked 5) 64 0 69 (@span_join (checked 5) 32 0 32 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) (@span_join (checked 5) 16 32 16 chunk5x32 chunk5x48)) (@span_join (checked 5) 32 64 37 (@span_join (checked 5) 16 64 16 chunk5x64 chunk5x80) (@span_join (checked 5) 16 96 21 chunk5x96 (@span_join (checked 5) 16 112 5 chunk5x112 chunk5x128))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 10 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 10 0 = true :=
  chunk6x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 1 0 = true :=
  chunk7x0
theorem verified : ∀ k ≤ 7, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 8 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 7
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    7 le_rfl 0 (by decide +kernel) k (by omega) run

end PrismSignedFrontier.SmallCert.Friend

namespace PrismSignedFrontier.SmallCert.Clique

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]
def target : W := 0xfee8fee8fee8fee8
def negative : List Nat := [0, 1, 2, 4, 8]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,9,by decide +kernel,?_⟩
    intro u hu diff
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xfff0fff0fff0fff0ffccffccffccffccffc0ffc0ffc0ffc0ffaaffaaffaaffaaffa8ffa8ffa8ffa8ff88ff88ff88ff88ff80ff80ff80ff80ff08ff08ff08ff08ff00ff00ff00ff00fefefefefefefefefcfcfcfcfcfcfcfcfcecfcecfcecfcecfcccfcccfcccfcccfafafafafafafafafaf0faf0faf0faf0faaafaaafaaafaaaf8f8f8f8f8f8f8f8f0f0f0f0f0f0f0f0f000f000f000f000eeeeeeeeeeeeeeeeeaeaeaeaeaeaeaeadcccdcccdcccdcccccccccccccccccccaaeeaaeeaaeeaaeeaaaaaaaaaaaaaaaaaaa8aaa8aaa8aaa8aa00aa00aa00aa00a8a8a8a8a8a8a8a88aaa8aaa8aaa8aaa88aa88aa88aa88aa8888888888888888808080808080808055005500550055002aaa2aaa2aaa2aaa0ff00ff00ff00ff00ccc0ccc0ccc0ccc0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a02aa02aa02aa02aa00fe00fe00fe00fe00ee00ee00ee00ee00aa00aa00aa00aa0088008800880088000a000a000a000a0000000000000000 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x2c854aa262c808b1752c814 else 0
  | 3 => if page < 1 then 0x6d650591b593a1b59491b58691f591b2b8946d650ab1650a69650ab1d5949db64e9dc594a5e59402c814b1a5889206c891b24891b6429db59495b59491b59099b59491b58b91b58891e58391b64e91b594 else 0
  | 4 => if page < 1 then 0x248db59491b5941246d6511ae96d651b59430391b6560e46d61c391b6565296d650391b5955246d650f91b5940646d650e91b65438091b64e91b6165276d650e0276d65246d650891b69620091b58891b5940a46d650d91b5940e46d6483 else 0
  | 5 => if page < 1 then 0x246d95940246d65030246d650e else 0
  | 6 => if page < 1 then 0x91b594 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 5
  | 3 => 27
  | 4 => 25
  | 5 => 3
  | 6 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 64
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 6)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (6*(k+1)) i)

def entries : ℕ → ℕ
  | 2 => 15
  | 3 => 52
  | 4 => 57
  | 5 => 24
  | 6 => 1
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0xf758bc7df5f20f42ee0d72b0e49b6c4abcd33116bc46ed82a7ac4a8c8ebcdb37896ec0eb87fb08ac6a832aa5695a29a134532674071e30f304a4b52f else 0
  | 3 => if page < 1 then 0xf8e62223f5f20f42f2ce932dee0d72b0e2683b2ede093731d0de7401ccdd1580c4f878eec3be5370c32e1bcbbca42527bc0432d4b3a4ade1b0f17f4ea5c54e09a435a9e09fa81fff9de0b1779bbe48469b280c879aad417f955e25bd8d7fc14a89a2ce1689168a8286adaff8869761bc84b1148f81cb1ffb7dcc3f4375b6eec5717d089670b1821d6f5bd5626bce49836475044d5ee60eea53af55cb52917250451b7f22416e30e3402960923f2bd5e737473955335d9a7c1631a5f711f6e0660cfc01e60b3e2cb20534d1610171030f else 0
  | 4 => if page < 1 then 0xf8e62223f81fd78df6ba7915f69ad12df637dcdaef65f957ed40eaa1e8e1e6a4e772fe93e3e70824df50a193da73095fd4861404d1081016cfb8e322cd46f8eaccdd1580c4f878eebc3b8250bc062322b77623f9b0bb71b4aff810f6a90469f2a8b960eaa7c97a3fa02449639fa81fff9aad417f9aa959ae92ef391291865f6b8fd8b55c7ee970787a3484d579cdd64e6e3f1d236d74642d6c86272c61eb4e8d6023c9505471fb9d53610a104ca1f5034c5841c848c3425f39c18bdb3526aae52d95698f255586ae2256bd941cee8fb21ceba3101616dc250e323f930b8dc12507ce1276 else 0
  | 5 => if page < 1 then 0xf81fd78df5c0eceff45ec061e0cdfcf7d4861404d094aa8ecfd12861c7273b9eaae446f49368853b84ec76277a6b3f6f6e557ea06e3f1d235c3e725c4d06dc334c3774b944036a87300faceb2ee5d9ed2c779505255586ae1f706beb0f3d84ff else 0
  | 6 => if page < 1 then 0x869761bc else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x3000110010000c0040000600000002008d00310090000300680050000f else 0
  | 3 => if page < 1 then 0x2001b100d001b00052017001200101010002300063010401210042008901c50223007001c40060032900710180004001600116004400000023014000a0023102c002f501d20290028c00e1034002c202c70300006d0201020002a802700190019101e0025002c1 else 0
  | 4 => if page < 1 then 0x140002401a002b201b10240001200b0030100b101e8026102230204021202a400e100e001d30200024201e6006202c90160006002600090009101280061000402e102b3016601d6018300d002c80280030001b000410129004002e0029502670000003200d101a202a50101010002620266 else 0
  | 5 => if page < 1 then 0x240020004c0040004300340000002a000c0028000d003500020003002700100042004d00210026002b003200290050 else 0
  | 6 => if page < 1 then 0x0 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def search (k h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if field keys k 32 m ≤ h then search k h fuel m hi else search k h fuel lo m
    else lo

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let ix := search k (key xs) 14 0 (entries k)
  let slot := field targets k 16 ix
  (slot / 32,slot % 32)

def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s23]
  | 2 => [s12]
  | 3 => [s12, s13]
  | 4 => [s13, s12]
  | 5 => [s13]
  | 6 => [s01]
  | 7 => [s01, s23]
  | 8 => [s01, s02]
  | 9 => [s01, s02, s03]
  | 10 => [s01, s03, s02]
  | 11 => [s01, s03]
  | 12 => [s02, s01]
  | 13 => [s02, s01, s13]
  | 14 => [s02]
  | 15 => [s02, s03]
  | 16 => [s02, s13]
  | 17 => [s02, s13, s01]
  | 18 => [s03, s01, s12]
  | 19 => [s03, s01]
  | 20 => [s03, s02]
  | 21 => [s03]
  | 22 => [s03, s12, s01]
  | 23 => [s03, s12]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s23_ok, s12_ok, s13_ok, s01_ok, s02_ok, s03_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel


def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 6 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 5 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x16 : span (checked 3) 11 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 27 0 = true :=
  (@span_join (checked 3) 16 0 11 chunk3x0 chunk3x16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x16 : span (checked 4) 9 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 25 0 = true :=
  (@span_join (checked 4) 16 0 9 chunk4x0 chunk4x16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 3 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 3 0 = true :=
  chunk5x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 1 0 = true :=
  chunk6x0
theorem verified : ∀ k ≤ 6, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 7 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 6
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    6 le_rfl 0 (by decide +kernel) k (by omega) run

end PrismSignedFrontier.SmallCert.Clique
