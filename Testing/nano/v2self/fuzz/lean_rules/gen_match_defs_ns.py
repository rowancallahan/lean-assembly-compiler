D="/tmp/claude-0/lr/cases3"
IN="-- input (hex): 61 02 03\n"
def Mt(body,pre=""): return IN+pre+f"def m (x : List UInt8) : List UInt8 := put [] ({body})\n"
c={}
# match
c["m01_basic"]=Mt("match rd x 0 with | 97 => 1 | 98 => 2 | _ => 3")
c["m02_dup_literal"]=Mt("match rd x 0 with | 97 => 1 | 97 => 2 | _ => 3")
c["m03_dup_wrap"]=Mt("match rd x 1 with | 0 => 1 | 18446744073709551616 => 2 | _ => 3")
c["m04_big_pat"]=Mt("match rd x 1 with | 18446744073709551618 => 1 | _ => 3")
c["m05_only_wild"]=Mt("match rd x 0 with | _ => 3")
c["m06_only_var"]=Mt("match rd x 0 with | v => v + 1")
c["m07_pair_first"]=Mt("match (rd x 0, rd x 1) with | (a, b) => a + b")
c["m08_arm_after_wild"]=Mt("match rd x 0 with | _ => 3 | 97 => 4")
c["m09_nonexhaustive"]=Mt("match rd x 0 with | 97 => 3")
c["m10_arms_misaligned"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (match rd x 0 with\n    | 97 => 1\n  | _ => 3)\n"
c["m11_rhs_col_lt_bar"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (match rd x 0 with\n  | 97 =>\n1\n  | _ => 3)\n"
c["m12_arms_same_line"]=Mt("match rd x 0 with | 97 => 1 | _ => 3")
c["m13_nested_match_arm"]=Mt("match rd x 0 with | 97 => (match rd x 1 with | 2 => 5 | _ => 6) | _ => 3")
c["m14_nested_unparen"]=Mt("match rd x 0 with | 97 => match rd x 1 with | 2 => 5 | _ => 6 | _ => 3")
c["m15_scrut_literal"]=Mt("match 3 with | 3 => 1 | _ => 2")
c["m16_pat_sub"]=Mt("match rd x 0 with | 96 + 1 => 1 | _ => 2")
c["m17_or_pat"]=Mt("match rd x 0 with | 97 | 98 => 1 | _ => 2")
c["m18_var_arm_shadow"]=Mt("match rd x 0 with | 5 => 1 | rd => rd")
c["m19_match_in_let"]=Mt("let y := match rd x 0 with | 97 => 1 | _ => 2; y + 1")
c["m20_match_at_def_top"]=IN+"def f (b : UInt64) : UInt64 := match b with\n  | 97 => 1\n  | _ => 2\ndef m (x : List UInt8) : List UInt8 := put [] (f (rd x 0))\n"
c["m21_match_bar_col0"]=IN+"def f (b : UInt64) : UInt64 := match b with\n| 97 => 1\n| _ => 2\ndef m (x : List UInt8) : List UInt8 := put [] (f (rd x 0))\n"
c["m22_pair_second_arm"]=Mt("match (rd x 0, rd x 1) with | (1, b) => 1 | (a, b) => a + b")
c["m23_wild_var_pair"]=Mt("match (rd x 0, rd x 1) with | (_, b) => b")
# fuel loops / defs
FL="def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a => a\n  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\n"
c["d01_loop_ok"]=IN+FL+"def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d02_loop_bars_misaligned"]=IN+"def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n    | 0, x, i, a => a\n  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\ndef m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d03_loop_bar_col0"]=IN+"def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n| 0, x, i, a => a\n| n + 1, x, i, a => f n x (i + 1) (a + rd x i)\ndef m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d04_loop_rhs_col0"]=IN+"def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n  | 0, x, i, a =>\na\n  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\ndef m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d05_loop_one_line"]=IN+"def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64 | 0, x, i, a => a | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\ndef m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d06_loop_arms_swapped"]=IN+"def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)\n  | 0, x, i, a => a\ndef m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d07_loop_k_plus_2"]=IN+"def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 2, a => a\ndef m (x : List UInt8) : List UInt8 := put [] (f 3 1)\n"
c["d08_nonterminating_fuel"]=IN+"def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => f (n + 1) (a + 1)\ndef m (x : List UInt8) : List UInt8 := put [] (f 3 1)\n"
c["d09_two_defs_order"]=IN+"def a (v : UInt64) : UInt64 := b v\ndef b (v : UInt64) : UInt64 := v\ndef m (x : List UInt8) : List UInt8 := put [] (a 1)\n"
c["d10_self_nontail"]=IN+"def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => f n a + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 3 1)\n"
c["d11_no_m"]="def a (v : UInt64) : UInt64 := v\n"
c["d12_m_wrong_type"]="def m (x : UInt64) : UInt64 := x\n"
c["d13_where"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (g 1)\n  where g (v : UInt64) : UInt64 := v + 1\n"
c["d14_partial"]=IN+"partial def f (v : UInt64) : UInt64 := if v == 5 then v else f (v + 1)\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d15_ret_type_missing"]=IN+"def f (v : UInt64) := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d16_param_type_missing"]=IN+"def f (v) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d17_private"]=IN+"private def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d18_private_expr"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (private 1)\n"
c["d19_protected_def"]=IN+"protected def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d20_noncomputable"]=IN+"noncomputable def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d21_abbrev"]=IN+"abbrev f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d22_theorem_between"]=IN+"theorem t : 1 = 1 := rfl\n"+"def m (x : List UInt8) : List UInt8 := put [] 1\n"
c["d23_implicit_binder"]=IN+"def f {a : UInt64} (v : UInt64) : UInt64 := v\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d24_fun"]=IN+"def m (x : List UInt8) : List UInt8 := put [] ((fun (v : UInt64) => v + 1) 1)\n"
c["d25_hash_eval"]=IN+"#eval 1\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["d26_set_option"]=IN+"set_option maxRecDepth 100 in\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["d27_inline_attr"]=IN+"@[inline] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d28_unknown_attr"]=IN+"@[bogus] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d29_implemented_by"]=IN+"def g (v : UInt64) : UInt64 := v + 100\n@[implemented_by g] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d30_attr_inline_loop"]=IN+"@[inline] "+FL+"def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)\n"
c["d31_export_attr"]=IN+"@[export my_f] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d32_attr_two"]=IN+"@[inline, simp] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d33_attr_comment_hides_bracket"]=IN+"@[inline -- ]\n] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d34_attr_after_private"]=IN+"private @[inline] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["d35_attr_on_m"]=IN+"@[inline] def m (x : List UInt8) : List UInt8 := put [] 1\n"
c["d36_attr_extern"]=IN+"@[extern my_f] def f (v : UInt64) : UInt64 := v + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
# namespaces
c["s01_ns_then_use_outside"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v + 1\nend A\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["s02_ns_use_inside"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v + 1\ndef g (v : UInt64) : UInt64 := f v\nend A\ndef m (x : List UInt8) : List UInt8 := put [] (A.g 1)\n"
c["s03_ns_qualified"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v + 1\nend A\ndef m (x : List UInt8) : List UInt8 := put [] (A.f 1)\n"
c["s04_open_use"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v + 1\nend A\nopen A\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["s05_end_mismatch"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v + 1\nend B\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s06_end_without_open"]=IN+"def f (v : UInt64) : UInt64 := v + 1\nend\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s07_missing_end"]=IN+"namespace A\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s08_open_unknown"]=IN+"open Foo\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s09_section_named_end_unnamed"]=IN+"section S\ndef m (x : List UInt8) : List UInt8 := put [] 1\nend\n"
c["s10_section_unnamed_end_named"]=IN+"section\ndef m (x : List UInt8) : List UInt8 := put [] 1\nend S\n"
c["s11_ns_dotted_end_partial"]=IN+"namespace A.B\ndef f (v : UInt64) : UInt64 := v\nend B\nend A\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s12_m_inside_ns"]=IN+"namespace A\ndef m (x : List UInt8) : List UInt8 := put [] 1\nend A\n"
c["s13_two_ns_same_name"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v\nend A\nnamespace B\ndef f (v : UInt64) : UInt64 := v + 1\nend B\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s14_open_in"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v + 1\nend A\ndef m (x : List UInt8) : List UInt8 := open A in put [] (f 1)\n"
c["s15_open_same_line"]=IN+"namespace A def f (v : UInt64) : UInt64 := v + 1\nend A\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s16_end_name_next_line_indented"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v\nend\n  A\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s17_end_in_cmt"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v\nend /- c -/ A\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s18_open_nat"]=IN+"open Nat\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s19_ns_shadow_root"]=IN+"def f (v : UInt64) : UInt64 := v\nnamespace A\ndef f (v : UInt64) : UInt64 := v + 1\ndef g (v : UInt64) : UInt64 := f v\nend A\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["s20_open_hiding_renaming"]=IN+"namespace A\ndef f (v : UInt64) : UInt64 := v\nend A\nopen A (f)\ndef m (x : List UInt8) : List UInt8 := put [] (f 1)\n"
c["s21_universe_variable"]=IN+"universe u\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
c["s22_section_variable"]=IN+"section\nvariable (k : UInt64)\ndef f : UInt64 := k\nend\ndef m (x : List UInt8) : List UInt8 := put [] 1\n"
# prims / semantic edges
c["p01_rd_oob"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (rd x 100)\n"
c["p02_bget_oob"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (bget (bpush bnew 7) 5)\n"
c["p03_bset_oob"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (bsize (bset (bpush bnew 7) 5 9))\n"
c["p04_bset_oob_get"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (bget (bset (bpush bnew 7) 5 9) 0)\n"
c["p05_put_trunc"]=IN+"def m (x : List UInt8) : List UInt8 := put (put [] 300) 257\n"
c["p06_len_vs_len'"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (len x)\n"
c["p07_bset_idx_huge"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (bsize (bset (bpush bnew 7) 18446744073709551616 9))\n"
c["p08_rd_idx_wrap"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (rd x 18446744073709551616)\n"
c["p09_empty_list_lit"]=IN+"def m (x : List UInt8) : List UInt8 := []\n"
c["p10_put_list_lit"]=IN+"def m (x : List UInt8) : List UInt8 := put (put [] 1) 2\n"
c["p11_tuple_param"]=IN+"def f (p : UInt64 × UInt64) : UInt64 := match p with | (a, b) => a - b\ndef m (x : List UInt8) : List UInt8 := put [] (f (1, 2))\n"
c["p12_let_tuple_scope"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (let (a, b) := (1, 2); let a := b; a)\n"
c["p13_tuple_triple"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (let (a, (b, c)) := (1, (2, 3)); a + b + c)\n"
c["p14_tuple_left_nest"]=IN+"def f (p : (UInt64 × UInt64) × UInt64) : UInt64 := 1\ndef m (x : List UInt8) : List UInt8 := put [] (f ((1, 2), 3))\n"
c["p15_arrow_type_curry"]=IN+"def f (a : UInt64) : UInt64 → UInt64 := fun b => a + b\ndef m (x : List UInt8) : List UInt8 := put [] (f 1 2)\n"
# typing/default
c["y01_let_lit_put"]=Mt("let a := 3; a - 4")
c["y02_let_lit_bind_then_cmp"]=Mt("let a := 3 - 4; if a == 0 then 1 else 2")
c["y03_cmp_lit_var"]=Mt("if 3 - 4 == rd x 1 then 1 else 2")
c["y04_cmp_var_lit"]=Mt("if rd x 1 - 4 == 3 - 4 then 1 else 2")
c["y05_match_scrut_lit"]=Mt("match 3 - 4 with | 0 => 1 | _ => 2")
c["y06_tuple_lit"]=Mt("let (a, b) := (3 - 4, 1); if a == 0 then 1 else 2")
c["y07_call_arg_lit"]=Mt("f 3 - 4","def f (v : UInt64) : UInt64 := v\n").replace("f 3 - 4","f (3 - 4)")
c["y08_if_branch_lit"]=Mt("if rd x 0 == 97 then 3 - 4 else 0")
c["y09_cmp_lit_lit_shift"]=Mt("if 1 <<< 64 == 1 then 1 else 2")
c["y10_cmp_lit_lit_big"]=Mt("if 18446744073709551616 == 0 then 1 else 2")
c["y11_cmp_lit_lit_big2"]=Mt("if 18446744073709551615 + 2 == 1 then 1 else 2")
c["y12_cmp_lit_lit_mul"]=Mt("if 3 * 5 == 15 then 1 else 2")
c["y13_cmp_lt_lit_wrap"]=Mt("if 5 < 3 - 4 then 1 else 2")
c["y14_lit_only_ctor"]=Mt("if 1 == 1 then 7 else 8")
c["y15_let_then_if_lit"]=Mt("let a := 5; let b := a - 6; if b < 1 then 1 else 2")
c["y16_let_use_u64_later"]=Mt("let a := 5; let b := a - 6; b + rd x 3")
c["y17_let_chain_cmp_nat"]=Mt("let a := 5; if a - 6 == 0 then 1 else 2")
c["y18_let_then_put_and_cmp"]=Mt("let a := 5; if a - 6 == 0 then a else 2")
c["y19_loop_init_lit"]="def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => f n (a - 1)\ndef m (x : List UInt8) : List UInt8 := put [] (f 2 0)\n"
c["y20_cond_both_sides_vars"]=Mt("if rd x 1 - 3 < rd x 2 then 1 else 2")
import os
for k,v in c.items(): open(f"{D}/{k}.lean","w",newline="").write(v)
print(len(c))
