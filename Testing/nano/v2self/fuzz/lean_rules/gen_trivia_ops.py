import os
import os
D=os.environ.get("CASES","/tmp/claude-0/lr/cases2")
def P(b,hdr="-- input (hex): 05 07 03\n"): return hdr+f"def m (x : List UInt8) : List UInt8 := put [] ({b})\n"
M="def m (x : List UInt8) : List UInt8 := put [] 1\n"
IN="-- input (hex): 05 07 03\n"
c={}
# trivia
c["t01_cmt_eof_nonl"]=M.rstrip("\n")+"\n-- trailing comment, no newline at EOF"
c["t02_nested_block"]="/- a /- b -/ c -/\n"+M
c["t03_block_dashdash_slash"]="/- x --/\n"+M
c["t04_block_slash_dash_slash"]="/-/ x -/\n"+M
c["t05_doc_before_def"]="/-- doc -/\n"+M
c["t06_doc_midexpr"]="def m (x : List UInt8) : List UInt8 := put [] (/-- d -/ 1)\n"
c["t07_moddoc_mid"]="def a (x : UInt64) : UInt64 := x\n/-! m -/\n"+M
c["t08_unterminated"]="/- x\n"+M
c["t09_cmt_in_expr"]="def m (x : List UInt8) : List UInt8 := put [] (1 /- c -/ + 2 -- d\n + 3)\n"
c["t10_tab_code"]="def m (x : List UInt8) : List UInt8 :=\tput [] 1\n"
c["t11_tab_in_comment"]="-- a\tb\n/- \t -/\n"+M
c["t12_crlf"]=M.replace("\n","\r\n")
c["t13_lone_cr_in_cmt"]="-- a\rb\n"+M
c["t14_arrow_dashdash"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (if rd x 0 <-- c\n rd x 1 then 1 else 2)\n"
c["t15_lt_slashdash"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (if rd x 0 </- c -/ rd x 1 then 1 else 2)\n"
c["t16_minus_minus_binary"]=IN+P("rd x 0 - -- c\n 1")
c["t17_block_in_line"]="-- /- not a block\n"+M
c["t18_dashdash_in_block"]="/- -- -/\n"+M
c["t19_attr_mid"]="def m (x : List UInt8) : List UInt8 := put [] (@[inline] 1)\n"
c["t20_unicode_cmt"]="-- λ × → ∀\n/- ü -/\n"+M
# identifiers
c["i01_charlit_name"]="def m (x : List UInt8) : List UInt8 := let 'a' := 1; put [] 1\n"
c["i02_quote_prefix"]="def m (x : List UInt8) : List UInt8 := let 'x := 1; put [] 1\n"
c["i03_underscore_use"]="def m (x : List UInt8) : List UInt8 := let _ := 1; put [] _\n"
c["i04_underscore_param"]="def f (_ : UInt64) : UInt64 := 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 2)\n"
c["i05_underscore_defname"]="def _ (a : UInt64) : UInt64 := a\n"+M
c["i06_kw_at"]="def m (x : List UInt8) : List UInt8 := let at := 1; put [] at\n"
c["i07_kw_fun"]="def fun (a : UInt64) : UInt64 := a\n"+M
c["i08_kw_sorry"]="def m (x : List UInt8) : List UInt8 := put [] sorry\n"
c["i09_kw_in_param"]="def f (in : UInt64) : UInt64 := in\ndef m (x : List UInt8) : List UInt8 := put [] (f 2)\n"
c["i10_root_clash_id"]="def id (a : UInt64) : UInt64 := a\n"+M
c["i11_root_clash_max"]="def max (a b : UInt64) : UInt64 := if a < b then b else a\n"+M
c["i12_prelude_clash_rd"]="def rd (a : UInt64) : UInt64 := a\n"+M
c["i13_ident_prime"]="def f' (a'' : UInt64) : UInt64 := a''\ndef m (x : List UInt8) : List UInt8 := put [] (f' 3)\n"
c["i14_dup_params"]="def f (a a : UInt64) : UInt64 := a\ndef m (x : List UInt8) : List UInt8 := put [] (f 1 2)\n"
c["i15_dup_params2"]="def f (a : UInt64) (a : UInt64) : UInt64 := a\ndef m (x : List UInt8) : List UInt8 := put [] (f 1 2)\n"
c["i16_param_shadows_def"]="def f (a : UInt64) : UInt64 := a + 1\ndef g (f : UInt64) : UInt64 := f\ndef m (x : List UInt8) : List UInt8 := put [] (g 7)\n"
c["i17_let_shadow"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 1; let a := a + 1; let b := (let a := 10; a) + a; b)\n"
c["i18_dot_name"]="def a.b (v : UInt64) : UInt64 := v\n"+M
c["i19_bang_name"]="def f! (v : UInt64) : UInt64 := v\n"+M
c["i20_guillemet"]="def «f» (v : UInt64) : UInt64 := v\n"+M
c["i21_digit_ident"]="def f1x (v : UInt64) : UInt64 := v\ndef m (x : List UInt8) : List UInt8 := put [] (f1x 4)\n"
c["i22_dup_def"]="def f (a : UInt64) : UInt64 := a\ndef f (a : UInt64) : UInt64 := a\n"+M
# numerals
c["n01_leading_zeros"]=P("007 + 00")
c["n02_wrap2e64"]=P("18446744073709551616 + 5")
c["n03_hex"]=P("0x10")
c["n04_bin"]=P("0b11")
c["n05_underscore"]=P("1_000")
c["n06_sci"]=P("1e3")
c["n07_decimal_point"]=P("1.5")
c["n08_octal"]=P("0o7")
c["n09_numword"]=P("1a")
c["n10_256_put"]=P("256 + 65")
c["n11_nat_lit_cmp"]="def m (x : List UInt8) : List UInt8 := put [] (if 3 - 4 == 0 then 1 else 2)\n"
c["n12_let_lit"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 3; if a - 4 == 0 then 1 else 2)\n"
c["n13_let_lit_then_u64"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 3; a - 4 + rd x 0)\n"
c["n14_lit_arith_in_put"]=P("3 - 4")
c["n15_lit_arith_mixed"]=P("3 - 4 + rd x 0")
c["n16_lit_lt"]="def m (x : List UInt8) : List UInt8 := put [] (if 18446744073709551615 + 1 == 0 then 1 else 2)\n"
c["n17_lit_mul_big"]="def m (x : List UInt8) : List UInt8 := put [] (if 4294967296 * 4294967296 == 0 then 1 else 2)\n"
c["n18_fuel_big"]="def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => if a == 3 then a else f n (a + 1)\ndef m (x : List UInt8) : List UInt8 := put [] (f 18446744073709551616 0)\n"
c["n19_fuel_small"]="def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => if a == 3 then a else f n (a + 1)\ndef m (x : List UInt8) : List UInt8 := put [] (f 2 0)\n"
c["n20_shl_64"]=P("rd x 0 <<< 64")
c["n21_shr_65"]=P("rd x 0 >>> 65")
c["n22_shl_var"]=P("rd x 0 <<< rd x 1")
c["n23_lit_cmp_lt_wrap"]="def m (x : List UInt8) : List UInt8 := put [] (if 0 - 1 < 5 then 1 else 2)\n"
c["n24_lit_shift_nat"]="def m (x : List UInt8) : List UInt8 := put [] (if 1 <<< 70 == 0 then 1 else 2)\n"
c["n25_lit_or"]="def m (x : List UInt8) : List UInt8 := put [] (if 1 ||| 2 == 3 then 1 else 2)\n"
# operators
c["o01_prec_mix"]=P("rd x 0 + rd x 1 * rd x 2 <<< 1 ||| 3 &&& 5 - 1")
c["o02_left_assoc_sub"]=P("rd x 0 - rd x 1 - rd x 2")
c["o03_shift_chain"]=P("rd x 0 <<< 2 <<< 1 >>> 1")
c["o04_and_or"]=P("rd x 0 ||| rd x 1 &&& rd x 2")
c["o05_eqchain"]="-- input (hex): 01\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 == 1 == 1 then 1 else 2)\n"
c["o06_lt_chain"]="-- input (hex): 01\ndef m (x : List UInt8) : List UInt8 := put [] (if 0 < rd x 0 < 3 then 1 else 2)\n"
c["o07_cond_arith"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 + 1 == rd x 1 then 1 else 2)\n"
c["o08_cond_or"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 ||| 1 == rd x 1 then 1 else 2)\n"
c["o09_dangling_else"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 == 1 then if rd x 1 == 5 then 7 else 8 else 9)\n"
c["o10_else_greedy"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 == 2 then 1 else 2 + rd x 1)\n"
c["o11_if_in_operand"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (1 + if rd x 0 == 1 then 2 else 3)\n"
c["o12_if_paren_op"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] ((if rd x 0 == 1 then 2 else 3) + 1)\n"
c["o13_if_multiline"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 :=\nput []\n(if rd x 0 == 1\nthen 2\nelse 3)\n"
c["o14_unary_minus"]=P("-rd x 0")
c["o15_ne"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 != 1 then 1 else 2)\n"
c["o16_le"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 <= 1 then 1 else 2)\n"
c["o17_gt"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 > 1 then 1 else 2)\n"
c["o18_and_andand"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if rd x 0 == 1 && rd x 1 == 2 then 1 else 2)\n"
c["o19_div"]=P("rd x 1 / rd x 0")
c["o20_mod_zero"]=P("rd x 1 % 0")
c["o21_pow"]=P("rd x 0 ^ 2")
c["o22_xor"]=P("rd x 0 ^^^ rd x 1")
c["o23_app_prec"]=P("rd x 0 + rd x 1")
c["o24_nested_paren_if_cond"]="-- input (hex): 01 02\ndef m (x : List UInt8) : List UInt8 := put [] (if (rd x 0) == (1) then (1) else (2))\n"
# let / app layout
c["l01_let_newline"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 5\n a + 1)\n"
c["l02_let_semi_newline"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 5;\n a + 1)\n"
c["l03_let_pair"]="def m (x : List UInt8) : List UInt8 := put [] (let (a, b) := (5, 6); a + b)\n"
c["l04_let_typed"]="def m (x : List UInt8) : List UInt8 := put [] (let a : UInt64 := 5; a + 1)\n"
c["l05_arg_col0"]="def m (x : List UInt8) : List UInt8 := put []\n1\n"
c["l06_body_col0"]="def m (x : List UInt8) : List UInt8 :=\nput [] 1\n"
c["l07_op_col0"]="def m (x : List UInt8) : List UInt8 := put [] (1\n+ 2)\n"
c["l08_app_arg_col0_top"]="def a (v : UInt64) : UInt64 := v\ndef m (x : List UInt8) : List UInt8 := put [] (a\n1)\n"
c["l09_let_body_col0"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 1;\na)\n"
c["l10_def_on_same_line"]="def a (v : UInt64) : UInt64 := v def m (x : List UInt8) : List UInt8 := put [] (a 1)\n"
c["l11_two_defs_no_nl"]="def a (v : UInt64) : UInt64 := v\ndef m (x : List UInt8) : List UInt8 := put [] (a 1) def z (v : UInt64) : UInt64 := v\n"
c["l12_const_def"]="def k : UInt64 := 41\ndef m (x : List UInt8) : List UInt8 := put [] (k + 1)\n"
c["l13_let_in_arg"]="def m (x : List UInt8) : List UInt8 := put [] (let a := 5; a) \n"
c["l14_let_tuple_nested"]="def m (x : List UInt8) : List UInt8 := put [] (let (a, b) := (5, 6); let (c, d) := (a, b); c + d)\n"
c["l15_empty_input"]="-- input (hex): \ndef m (x : List UInt8) : List UInt8 := put [] (rd x 0 + len x)\n"
os.makedirs(D, exist_ok=True)
for k, v in c.items(): open(f"{D}/{k}.lean", "w", newline="").write(v)
print(len(c), "cases ->", D)
