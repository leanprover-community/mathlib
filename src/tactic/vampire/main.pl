#!/usr/bin/env swipl

:- initialization(main, main).

:- [write, read, check].

parse_inp([num(Num) | Stk], ['f' | Chs], Mat) :-
  parse_inp([fn(Num) | Stk], Chs, Mat).

parse_inp([num(Num) | Stk], ['r' | Chs], Mat) :-
  parse_inp([rl(Num) | Stk], Chs, Mat).

parse_inp([Y, X | Stk], ['a' | Chs], Mat) :-
  parse_inp([app(X, Y) | Stk], Chs, Mat).

parse_inp([num(Num) | Stk], ['v' | Chs], Mat) :-
  parse_inp([var(Num) | Stk], Chs, Mat).

parse_inp([Y, X | Stk], ['q' | Tks], Mat) :-
  parse_inp([eq(X, Y) | Stk], Tks, Mat).

parse_inp([Atm | Stk], ['n' | Tks], Mat) :-
  parse_inp([lit(neg, Atm) | Stk], Tks, Mat).

parse_inp([Atm | Stk], ['p' | Tks], Mat) :-
  parse_inp([lit(pos, Atm) | Stk], Tks, Mat).

parse_inp(Stk, ['e' | Chs], Mat) :-
  parse_inp([[] | Stk], Chs, Mat).

parse_inp([Hd, Tl | Stk], ['c' | Chs], Mat) :-
  parse_inp([[Hd | Tl] | Stk], Chs, Mat).

parse_inp(Stk, ['b' | Chs], Mat) :-
  parse_inp([num(0) | Stk], Chs, Mat).

parse_inp([num(Num) | Stk], ['0' | Chs], Mat) :-
  NewNum is Num * 2,
  parse_inp([num(NewNum) | Stk], Chs, Mat).

parse_inp([num(Num) | Stk], ['1' | Chs], Mat) :-
  NewNum is (Num * 2) + 1,
  parse_inp([num(NewNum) | Stk], Chs, Mat).

parse_inp([Mat], [], Mat).

vnew_trm(fn(_), 0).

vnew_trm(var(NumA), NumB) :-
  NumB is NumA + 1.

vnew_trm(app(Trm1, Trm2), Num) :-
  vnew_trm(Trm1, Num1),
  vnew_trm(Trm2, Num2),
  max(Num1, Num2, Num).

vnew_atm(rl(_), 0).

vnew_atm(app(Atm, Trm), Num) :-
  vnew_atm(Atm, Num1),
  vnew_trm(Trm, Num2),
  max(Num1, Num2, Num).

vnew_atm(eq(Trm1, Trm2), Num) :-
  vnew_trm(Trm1, Num1),
  vnew_trm(Trm2, Num2),
  max(Num1, Num2, Num).

vnew_lit(lit(_, Atm), Num) :-
  vnew_atm(Atm, Num).

vnew_cla(Cla, Num) :-
  maplist(vnew_lit, Cla, Nums),
  max_list(Nums, Num).

offset(Ofs, Src, map(Src, var(Tgt))) :-
  Tgt is Src + Ofs.

vars_trm(fn(_), []).

vars_trm(app(Trm1, Trm2), Nums) :-
  vars_trm(Trm1, Nums1),
  vars_trm(Trm2, Nums2),
  union(Nums1, Nums2, Nums).

vars_trm(var(Num), [Num]).

vars_atm(rl(_), []).

vars_atm(app(Atm, Trm), Nums) :-
  vars_atm(Atm, Nums1),
  vars_trm(Trm, Nums2),
  union(Nums1, Nums2, Nums).

vars_atm(eq(TrmA, TrmB), Nums) :-
  vars_trm(TrmA, Nums1),
  vars_trm(TrmB, Nums2),
  union(Nums1, Nums2, Nums).

vars_lit(lit(_, Atm), Nums) :-
  vars_atm(Atm, Nums).

vars_cla(Cla, Nums) :-
  maplist(vars_lit, Cla, Numss),
  union(Numss, Nums).

disjoiner(Cla1, Cla2, Dsj) :-
  vnew_cla(Cla2, Num),
  vars_cla(Cla1, Nums),
  maplist(offset(Num), Nums, Dsj).

map_source(map(Src, _), Src).

domain(Maps, Dom) :-
  maplist(map_source, Maps, Dom).

in_domain(Dom, map(Src, _)) :-
  member(Src, Dom).

compose_maps(FstMaps, SndMaps, Maps) :-
  update_maps(FstMaps, SndMaps, NewFstMaps),
  domain(FstMaps, Dom),
  exclude(in_domain(Dom), SndMaps, NewSndMaps),
  append(NewFstMaps, NewSndMaps, Maps).

update_map(Map, map(Src, Tgt), map(Src, NewTgt)) :-
  subst_trm(Map, Tgt, NewTgt).

update_maps(FstMaps, SndMaps, NewFstMaps) :-
  maplist(update_map(SndMaps), FstMaps, NewFstMaps).

rep_trm(rgt, SrcTrm, TrmA, TrmB, TgtTrm, Rpl) :-
  unif_trm(SrcTrm, TrmA, RplA),
  subst_trm(RplA, TrmB, TrmB1),
  inst_trm(TrmB1, TgtTrm, RplB),
  compose_maps(RplA, RplB, Rpl).

rep_trm(_, fn(Num), _, _, fn(Num), []). 

rep_trm(rgt, var(Num), _, _, TgtTrm, [map(Num, TgtTrm)]).

rep_trm(_, app(SrcTrmA, SrcTrmB), TrmA, TrmB, app(TgtTrmA, TgtTrmB), Rpl) :- 
  rep_trm(lft, SrcTrmA, TrmA, TrmB, TgtTrmA, RplA), 
  subst_trm(RplA, SrcTrmB, SrcTrmB1),
  subst_trm(RplA, TrmA, TrmA1),
  subst_trm(RplA, TrmB, TrmB1),
  rep_trm(rgt, SrcTrmB1, TrmA1, TrmB1, TgtTrmB, RplB), 
  compose_maps(RplA, RplB, Rpl).

rep_atm(eq(SrcTrmA, SrcTrmB), TrmA, TrmB, eq(TgtTrmA, TgtTrmB), Rpl) :- 
  rep_trm(rgt, SrcTrmA, TrmA, TrmB, TgtTrmA, RplA), 
  subst_trm(RplA, SrcTrmB, SrcTrmB1),
  subst_trm(RplA, TrmA, TrmA1),
  subst_trm(RplA, TrmB, TrmB1),
  rep_trm(rgt, SrcTrmB1, TrmA1, TrmB1, TgtTrmB, RplB), 
  compose_maps(RplA, RplB, Rpl).

rep_atm(rl(Num), _, _, rl(Num), []). 

rep_atm(app(SrcAtm, SrcTrm), TrmA, TrmB, app(TgtAtm, TgtTrm), Rpl) :- 
  rep_atm(SrcAtm, TrmA, TrmB, TgtAtm, RplA), 
  subst_trm(RplA, SrcTrm, SrcTrm1),
  subst_trm(RplA, TrmA, TrmA1),
  subst_trm(RplA, TrmB, TrmB1),
  rep_trm(rgt, SrcTrm1, TrmA1, TrmB1, TgtTrm, RplB), 
  compose_maps(RplA, RplB, Rpl).

unif_trm(var(Num), Trm, [map(Num, Trm)]).
unif_trm(Trm, var(Num), [map(Num, Trm)]).

unif_trm(fn(Num), fn(Num), []).

unif_trm(app(Trm1, Trm2), app(Trm3, Trm4), Maps) :-
  unif_trm(Trm2, Trm4, FstMaps),
  subst_trm(FstMaps, Trm1, NewTrm1),
  subst_trm(FstMaps, Trm3, NewTrm3),
  unif_trm(NewTrm1, NewTrm3, SndMaps),
  compose_maps(FstMaps, SndMaps, Maps).

unif_atm(rl(Num), rl(Num), []).

unif_atm(app(AtmA, TrmA), app(AtmB, TrmB), Maps) :-
  unif_atm(AtmA, AtmB, FstMaps),
  subst_trm(FstMaps, TrmA, TrmA1),
  subst_trm(FstMaps, TrmB, TrmB1),
  unif_trm(TrmA1, TrmB1, SndMaps),
  compose_maps(FstMaps, SndMaps, Maps).

unif_atm(eq(TrmAL, TrmAR), eq(TrmBL, TrmBR), Maps) :-
  unif_trm(TrmAL, TrmBL, FstMaps),
  subst_trm(FstMaps, TrmAR, TrmAR1),
  subst_trm(FstMaps, TrmBR, TrmBR1),
  unif_trm(TrmAR1, TrmBR1, SndMaps),
  compose_maps(FstMaps, SndMaps, Maps).

range(0, Acc, Acc).

range(Num, Acc, Nums) :-
  0 < Num,
  NewNum is Num - 1,
  range(NewNum, [NewNum | Acc], Nums).

range(Num, Nums) :-
  range(Num, [], Nums).

member_rev(Lst, Elm) :- member(Elm, Lst).

merge_instantiators([], Inst, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, Inst) :-
  member(map(Idx, Tgt), Inst2),
  merge_instantiators(Inst1, Inst2, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, [map(Idx, Tgt) | Inst]) :-
  not(member(map(Idx, _), Inst2)),
  merge_instantiators(Inst1, Inst2, Inst).

inst_trm(var(Num), Trm, [map(Num, Trm)]).

inst_trm(fn(Num), fn(Num), []).

inst_trm(app(SrcTrmA, SrcTrmB), app(TgtTrmA, TgtTrmB), Maps) :-
  inst_trm(SrcTrmA, TgtTrmA, Maps1),
  inst_trm(SrcTrmB, TgtTrmB, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

inst_atm(rl(Num), rl(Num), []).

inst_atm(app(SrcAtm, SrcTrm), app(TgtAtm, TgtTrm), Maps) :-
  inst_atm(SrcAtm, TgtAtm, Maps1),
  inst_trm(SrcTrm, TgtTrm, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

inst_atm(eq(SrcTrmA, SrcTrmB), eq(TgtTrmA, TgtTrmB), Maps) :-
  inst_trm(SrcTrmA, TgtTrmA, Maps1),
  inst_trm(SrcTrmB, TgtTrmB, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

choose_map_atm(SrcAtm, TgtAtm, Maps) :- 
  inst_atm(SrcAtm, TgtAtm, Maps).

choose_map_atm(eq(TrmA, TrmB), TgtAtm, Maps) :- 
  inst_atm(eq(TrmB, TrmA), TgtAtm, Maps).

choose_map_lit(lit(Pol, SrcAtm), lit(Pol, TgtAtm), Maps) :-
  choose_map_atm(SrcAtm, TgtAtm, Maps).

choose_map_cla([], _, [], []).

choose_map_cla([Lit | Cla], Tgt, Maps, [LitNum | ClaNums]) :-
  nth0(LitNum, Tgt, TgtLit),
  choose_map_lit(Lit, TgtLit, LitMaps),
  choose_map_cla(Cla, Tgt, ClaMaps, ClaNums),
  merge_instantiators(LitMaps, ClaMaps, Maps).

surjective(Ran, Nums) :-
  length(Ran, Lth),
  range(Lth, Idxs),
  subset(Idxs, Nums).

count(_, [], 0).

count(Elm, [Elm | Lst], Cnt) :-
  count(Elm, Lst, Tmp),
  Cnt is Tmp + 1.

count(Elm, [Hd | Lst], Cnt) :-
  not(Elm = Hd),
  count(Elm, Lst, Cnt).

dup_idxs([Hd | Tl], 0, Idx) :-
  nth1(Idx, Tl, Hd).

dup_idxs([_ | Tl], IdxA, IdxB) :-
  dup_idxs(Tl, SubIdxA, SubIdxB),
  IdxA is SubIdxA + 1,
  IdxB is SubIdxB + 1.

conc(asm(_, Cnc), Cnc).
conc(rsl(_, _, Cnc), Cnc).
conc(rtt(_, _, Cnc), Cnc).
conc(cnt(_, Cnc), Cnc).
conc(sub(_, _, Cnc), Cnc).
conc(rep(_, _, Cnc), Cnc).
conc(sym(_, Cnc), Cnc).
conc(trv(_, Cnc), Cnc).

allign_eq(Prf, Prf) :-
  conc(Prf, [Lit, Lit | _]).

allign_eq(SubPrf, Prf) :-
  conc(SubPrf, [lit(Pol, eq(TrmA, TrmB)), lit(Pol, eq(TrmB, TrmA)) | Cnc]),
  Prf = sym(SubPrf, [lit(Pol, eq(TrmB, TrmA)), lit(Pol, eq(TrmB, TrmA)) | Cnc]).

compile_cnts(Prf, Dsts, Prf) :-
  not(dup_idxs(Dsts, _, _)).

compile_cnts(SubPrf, Dsts, Prf) :-
  dup_idxs(Dsts, IdxA, IdxB),
  conc(SubPrf, SubCnc),
  tor(SubCnc, IdxA, SubCnc1),
  SubPrf1 = rtt(IdxA, SubPrf, SubCnc1),
  tor(SubCnc1, IdxB, [Lit1, Lit2 | SubCnc2]),
  SubPrf2 = rtt(IdxB, SubPrf1, [Lit1, Lit2 | SubCnc2]),
  allign_eq(SubPrf2, SubPrf3),
  conc(SubPrf3, [Lit, Lit | SubCnc3]),
  SubPrf4 = cnt(SubPrf3, [Lit | SubCnc3]),
  tor(Dsts,  IdxA, Dsts1),
  tor(Dsts1, IdxB, [Dst, Dst | Dsts2]),
  compile_cnts(SubPrf4, [Dst | Dsts2], Prf).

compute_maps(Cla, Tgt, Maps, Nums) :-
  choose_map_cla(Cla, Tgt, Maps, Nums),
  surjective(Tgt, Nums).

compile_map(SubPrf, Tgt, Prf) :-
  conc(SubPrf, SubCnc),
  compute_maps(SubCnc, Tgt, Inst, Nums),
  subst_cla(Inst, SubCnc, SubCnc1),
  compile_cnts(sub(Inst, SubPrf, SubCnc1), Nums, Prf).

rep_lit(lit(Pol, SrcAtm), TrmA, TrmB, lit(Pol, TgtAtm), Rpl) :-
  rep_atm(SrcAtm, TrmA, TrmB, TgtAtm, Rpl). 

compile_rep_core(PrfA, PrfB, TgtLit, Prf) :-
  conc(PrfA, [Lit]),
  conc(PrfB, [lit(pos, eq(TrmA, TrmB))]),
  disjoiner([Lit], [TgtLit], Dsj1),
  subst_lit(Dsj1, Lit, Lit1),
  disjoiner([lit(pos, eq(TrmA, TrmB))], [Lit1], Dsj2),
  subst_trm(Dsj2, TrmA, TrmA1),
  subst_trm(Dsj2, TrmB, TrmB1),
  PrfA1 = sub(Dsj1, PrfA, [Lit1]),
  PrfB1 = sub(Dsj2, PrfB, [lit(pos, eq(TrmA1, TrmB1))]),
  rep_lit(Lit1, TrmA1, TrmB1, TgtLit, Rpl), 
  subst_lit(Rpl, Lit1, Lit2),
  PrfA2 = sub(Rpl, PrfA1, [Lit2]),
  subst_cla(Rpl, [lit(pos, eq(TrmA1, TrmB1))], Cnc),
  PrfB2 = sub(Rpl, PrfB1, Cnc),
  Prf = rep(PrfA2, PrfB2, [TgtLit]).

select_dir(Prf, Prf).

select_dir(Prf, NewPrf) :- 
  conc(Prf, [lit(Pol, eq(TrmA, TrmB)) | Cnc]),
  NewPrf = sym(Prf, [lit(Pol, eq(TrmB, TrmA)) | Cnc]).

compile_rep(PrfA, PrfB, TgtLit, Prf) :-
  select_dir(PrfA, NewPrfA), 
  select_dir(PrfB, NewPrfB), 
  compile_rep_core(NewPrfA, NewPrfB, TgtLit, Prf).

compile_rsl(PrfA, PrfB, rsl(PrfA2, PrfB1, Cnc)) :-
  conc(PrfA, CncA),
  CncA = [lit(neg, _) | _],
  conc(PrfB, CncB),
  CncB = [lit(pos, AtmB) | _],
  disjoiner(CncA, CncB, Dsj),
  subst_cla(Dsj, CncA, CncA1),
  CncA1 = [lit(neg, AtmA) | _],
  PrfA1 = sub(Dsj, PrfA, CncA1),
  unif_atm(AtmA, AtmB, Unf),
  subst_cla(Unf, CncA1, CncA2),
  CncA2 = [lit(neg, Atm) | ClaA2],
  PrfA2 = sub(Unf, PrfA1, CncA2),
  subst_cla(Unf, CncB, CncB1),
  CncB1 = [lit(pos, Atm) | ClaB1],
  PrfB1 = sub(Unf, PrfB, CncB1),
  append(ClaA2, ClaB1, Cnc).

compile(Mat, _, Num, Tgt, asm, Prf) :-
  nth0(Num, Mat, Cla),
  compile_map(asm(Num, Cla), Tgt, Prf).

compile(Mat, Lns, _, Tgt, rsl(NumA, NumB), Prf) :-
  compile(Mat, Lns, NumA, PrfA),
  compile(Mat, Lns, NumB, PrfB),
  conc(PrfA, CncA),
  conc(PrfB, CncB),
  tor(CncA, IdxA, CncA1),
  tor(CncB, IdxB, CncB1),
  PrfA1 = rtt(IdxA, PrfA, CncA1),
  PrfB1 = rtt(IdxB, PrfB, CncB1),
  ( compile_rsl(PrfA1, PrfB1, SubPrf) ;
    compile_rsl(PrfB1, PrfA1, SubPrf) ),
  compile_map(SubPrf, Tgt, Prf).

compile(Mat, Lns, _, [TgtLit], rep(NumA, NumB), Prf) :-
  compile(Mat, Lns, NumA, PrfA),
  compile(Mat, Lns, NumB, PrfB),
  compile_rep(PrfA, PrfB, TgtLit, Prf).

compile(Mat, Lns, _, Tgt, eqres(Num), Prf) :-
  compile(Mat, Lns, Num, Prf1),
  conc(Prf1, Cnc1),
  tor(Cnc1, Idx, Cnc2), 
  Cnc2 = [lit(neg, eq(TrmA, TrmB)) | _],
  Prf2 = rtt(Idx, Prf1, Cnc2),
  unif_trm(TrmA, TrmB, Unf),
  subst_cla(Unf, Cnc2, Cnc3),
  Cnc3 = [lit(neg, eq(Trm, Trm)) | Tl],
  Prf3 = sub(Unf, Prf2, Cnc3),
  Prf4 = trv(Prf3, Tl),
  compile_map(Prf4, Tgt, Prf).

compile(Mat, Lns, _, Tgt, trv(Num), trv(Prf, Tgt)) :-
  compile(Mat, Lns, Num, Prf),
  conc(Prf, [lit(neg, eq(Trm, Trm)) | Tgt]).

compile(Mat, Lns, _, Tgt, map(Num), Prf) :-
  compile(Mat, Lns, Num, SubPrf),
  compile_map(SubPrf, Tgt, Prf).

compile(Mat, Lns, Num, Prf) :-
  member(line(Num, Tgt, Rul), Lns),
  compile(Mat, Lns, Num, Tgt, Rul, Prf).

dezerortt(asm(Num, Maps), asm(Num, Maps)).

dezerortt(rtt(0, Prf), CPrf) :-
  dezerortt(Prf, CPrf).

dezerortt(rtt(Num, Prf), rtt(Num, CPrf)) :-
  0 < Num,
  dezerortt(Prf, CPrf).

dezerortt(rsl(PrfA, PrfB), rsl(PrfA1, PrfB1)) :-
  dezerortt(PrfA, PrfA1),
  dezerortt(PrfB, PrfB1).

dezerortt(rep(PrfA, PrfB), rep(PrfA1, PrfB1)) :-
  dezerortt(PrfA, PrfA1),
  dezerortt(PrfB, PrfB1).

dezerortt(trv(Prf), trv(CPrf)) :-
  dezerortt(Prf, CPrf).

dezerortt(sym(Prf), sym(CPrf)) :-
  dezerortt(Prf, CPrf).

dezerortt(cnt(Prf), cnt(CPrf)) :-
  dezerortt(Prf, CPrf).

relevant(Vars, map(Num, _)) :-
  member(Num, Vars).

filter_maps(Prf, Maps, NewMaps) :-
  conc(Prf, Cnc),
  vars_cla(Cnc, Vars),
  include(relevant(Vars), Maps, NewMaps).

% pushmaps_debug(Maps, asm(_, Cnc), passed(Cla)) :-
%   vars(Cnc, Vars),
%   include(relevant(Vars), Maps, NewMaps),
%   subst(Maps, Cnc, Cla),
%   subst(NewMaps, Cnc, Cla).
%
% pushmaps_debug(Maps, asm(Num, Cnc), failed(Maps, asm(Num, Cnc))) :-
%   vars(Cnc, Vars),
%   include(relevant(Vars), Maps, NewMaps),
%   subst(Maps, Cnc, ClaA),
%   subst(NewMaps, Cnc, ClaB),
%   not(ClaA = ClaB).
%
% pushmaps_debug(Maps, rsl(PrfA, _, _), failed(X, Y)) :-
%   filter_maps(PrfA, Maps, MapsA),
%   pushmaps_debug(MapsA, PrfA, failed(X, Y)).
%
% pushmaps_debug(Maps, rsl(_, PrfB, _), failed(X, Y)) :-
%   filter_maps(PrfB, Maps, MapsB),
%   pushmaps_debug(MapsB, PrfB, failed(X, Y)).
%
% pushmaps_debug(Maps, rsl(PrfA, PrfB, Cnc), Rst) :-
%   filter_maps(PrfA, Maps, MapsA),
%   filter_maps(PrfB, Maps, MapsB),
%   (
%     pushmaps_debug(MapsA, PrfA, passed([lit(neg, Trm) | ClaA])),
%     pushmaps_debug(MapsB, PrfB, passed([lit(pos, Trm) | ClaB])),
%     subst(Maps, Cnc, Cla),
%     append(ClaA, ClaB, Cla)
%   ) -> Rst = passed(Cla) ; Rst  = failed(Maps, rsl(PrfA, PrfB, Cnc)).
%
% pushmaps_debug(Maps, rtt(_, Prf, _), failed(X, Y)) :-
%   pushmaps_debug(Maps, Prf, failed(X, Y)).
%
% pushmaps_debug(Maps, rtt(Num, PrfA, CncA), passed(Cnc)) :-
%   pushmaps_debug(Maps, PrfA, passed(CncB)),
%   rot(Num, CncB, Cnc),
%   subst(Maps, CncA, Cnc).
%
% pushmaps_debug(MapsA, sub(MapsB, Prf, _), failed(X, Y)) :-
%   compose_maps(MapsB, MapsA, Maps),
%   pushmaps_debug(Maps, Prf, failed(X, Y)).
%
% pushmaps_debug(MapsA, sub(MapsB, Prf, CncB), passed(Cnc)) :-
%   compose_maps(MapsB, MapsA, Maps),
%   pushmaps_debug(Maps, Prf, passed(Cnc)),
%   subst(MapsA, CncB, Cnc).

% pushmaps_debug(Maps, cnt(Prf, _), failed(X, Y)) :-
%   pushmaps_debug(Maps, Prf, failed(X, Y)).
%
% pushmaps_debug(Maps, cnt(PrfA, CncA), passed([Lit | Cla])) :-
%   pushmaps_debug(Maps, PrfA, passed([Lit, Lit | Cla])),
%   subst(Maps, CncA, [Lit | Cla]).
% instantiation
% rotation
% resolution
% contraction
% substitution
% symmetry

pushmaps(Maps, asm(Num, Cnc), asm(Num, NewMaps)) :-
  vars_cla(Cnc, Vars),
  include(relevant(Vars), Maps, NewMaps).

pushmaps(Maps, rsl(PrfA, PrfB, _), rsl(CPrfA, CPrfB)) :-
  filter_maps(PrfA, Maps, MapsA),
  filter_maps(PrfB, Maps, MapsB),
  pushmaps(MapsA, PrfA, CPrfA),
  pushmaps(MapsB, PrfB, CPrfB).

pushmaps(Maps, rep(PrfA, PrfB, _), rep(CPrfA, CPrfB)) :-
  filter_maps(PrfA, Maps, MapsA),
  filter_maps(PrfB, Maps, MapsB),
  pushmaps(MapsA, PrfA, CPrfA),
  pushmaps(MapsB, PrfB, CPrfB).

pushmaps(Maps, sym(Prf, _), sym(CPrf)) :-
  pushmaps(Maps, Prf, CPrf).

pushmaps(Maps, rtt(Num, Prf, _), rtt(Num, CPrf)) :-
  pushmaps(Maps, Prf, CPrf).

pushmaps(MapsA, sub(MapsB, Prf, _), CPrf) :-
  compose_maps(MapsB, MapsA, Maps),
  pushmaps(Maps, Prf, CPrf).

pushmaps(Maps, cnt(Prf, _), cnt(CPrf)) :-
  pushmaps(Maps, Prf, CPrf).

pushmaps(Maps, trv(Prf, _), trv(CPrf)) :-
  pushmaps(Maps, Prf, CPrf).

pushmaps(Prf, CPrf) :-
  pushmaps([], Prf, CPrf).

groundterm(var(_), fn(0)).

groundterm(fn(Num), fn(Num)).

groundterm(app(TrmA, TrmB), app(GndTrmA, GndTrmB)) :-
  groundterm(TrmA, GndTrmA),
  groundterm(TrmB, GndTrmB).

groundmap(map(Num, Trm), map(Num, NewTrm)) :-
  groundterm(Trm, NewTrm).

groundmaps(asm(Num, Maps), asm(Num, NewMaps)) :-
  maplist(groundmap, Maps, NewMaps).

groundmaps(rsl(PrfA, PrfB), rsl(PrfA1, PrfB1)) :-
  groundmaps(PrfA, PrfA1),
  groundmaps(PrfB, PrfB1).

groundmaps(rep(PrfA, PrfB), rep(PrfA1, PrfB1)) :-
  groundmaps(PrfA, PrfA1),
  groundmaps(PrfB, PrfB1).

groundmaps(trv(Prf), trv(Prf1)) :-
  groundmaps(Prf, Prf1).

groundmaps(sym(Prf), sym(Prf1)) :-
  groundmaps(Prf, Prf1).

groundmaps(rtt(Num, Prf), rtt(Num, Prf1)) :-
  groundmaps(Prf, Prf1).

groundmaps(cnt(Prf), cnt(Prf1)) :-
  groundmaps(Prf, Prf1).

compress(RawPrf, Prf) :-
  pushmaps(RawPrf, Prf1),
  dezerortt(Prf1, Prf2),
  groundmaps(Prf2, Prf).

compress(RawPrf, compress_error(RawPrf)).

compile(Mat, Lns, Prf) :-
  length(Lns, Lth),
  Idx is Lth - 1,
  nth0(Idx, Lns, line(Num, [], Rul)),
  compile(Mat, Lns, Num, [], Rul, Prf).

compile(Mat, Lns, compile_error(Mat, Lns)).

string_block(Str, Blk) :-
  break_string(60, Str, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Blk).

trm_string(var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

trm_string(fn(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("f", NumStr, Str).

trm_string(app(TrmA, TrmB), Str) :-
  trm_string(TrmA, StrA),
  trm_string(TrmB, StrB),
  join_string(["(", StrA, " ", StrB, ")"], Str).

atm_string(rl(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("r", NumStr, Str).

atm_string(app(Atm, Trm), Str) :-
  atm_string(Atm, StrA),
  trm_string(Trm, StrB),
  join_string(["(", StrA, " ", StrB, ")"], Str).

lit_string(lit(pos, Atm), Str) :-
  atm_string(Atm, Str).

lit_string(lit(neg, Trm), Str) :-
  trm_string(Trm, Str1),
  string_concat("-", Str1, Str).

map_string(map(Num, Trm), Str) :-
  number_string(Num, NumStr),
  trm_string(Trm, TrmStr),
  join_string([NumStr, " |-> ", TrmStr], Str).

list_string(ItemString, Lst, Str) :-
  maplist(ItemString, Lst, Strs),
  join_string(Strs, ", ", TmpStr),
  join_string(["[", TmpStr, "]"], Str).

cla_string(Cla, Str) :-
  list_string(lit_string, Cla, Str).

maps_string(Maps, Str) :-
  list_string(map_string, Maps, Str).

cproof_string(Mat, Spcs, asm(Num, Maps), Str, Cnc) :-
  string_concat("  ", Spcs, NewSpcs),
  nth0(Num, Mat, Cla),
  subst_cla(Maps, Cla, Cnc),
  cla_string(Cnc, CncStr),
  number_string(Num, NumStr),
  maps_string(Maps, MapsStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "asm ", NumStr, " : ", CncStr, Nl, NewSpcs, MapsStr], Str).

cproof_string(Mat, Spcs, rsl(PrfA, PrfB), Str, Cnc) :-
  string_concat("  ", Spcs, NewSpcs),
  cproof_string(Mat, NewSpcs, PrfA, StrA, [_ | CncA]), !,
  cproof_string(Mat, NewSpcs, PrfB, StrB, [_ | CncB]), !,
  append(CncA, CncB, Cnc),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rsl : ", CncStr, Nl, StrA, Nl, StrB], Str).

cproof_string(Mat, Spcs, rtt(Num, PrfA), Str, Cnc) :-
  string_concat("  ", Spcs, NewSpcs),
  number_string(Num, NumStr),
  cproof_string(Mat, NewSpcs, PrfA, StrA, CncA), !,
  rot(Num, CncA, Cnc),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rtt ", NumStr, " : ", CncStr, Nl, StrA], Str).

cproof_string(Mat, Spcs, cnt(PrfA), Str, [Lit | Cla]) :-
  string_concat("  ", Spcs, NewSpcs),
  cproof_string(Mat, NewSpcs, PrfA, StrA, [Lit, Lit | Cla]), !,
  cla_string([Lit | Cla], CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "cnt : ", CncStr, Nl, StrA], Str).

cproof_string(Mat, Prf, Str) :-
  cproof_string(Mat, "", Prf, Str, _).

proof_string(Spcs, asm(Num, Cnc), Str) :-
  number_string(Num, NumStr),
  cla_string(Cnc, CncStr),
  join_string([Spcs, "asm ", NumStr, " : ", CncStr], Str).

proof_string(Spcs, rsl(PrfA, PrfB, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  proof_string(NewSpcs, PrfB, StrB),
  string_codes(Nl, [10]),
  join_string([Spcs, "rsl : ", CncStr, Nl, StrA, Nl, StrB], Str).

proof_string(Spcs, sub(Maps, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  maps_string(Maps, MapsStr),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  string_codes(Nl, [10]),
  join_string([Spcs, "sub : ", CncStr, Nl, NewSpcs, MapsStr, Nl, StrA], Str).

proof_string(Spcs, rtt(Num, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  number_string(Num, NumStr),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rtt ", NumStr, " : ", CncStr, Nl, StrA], Str).

proof_string(Spcs, cnt(PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "cnt : ", CncStr, Nl, StrA], Str).

proof_string(Prf, Str) :-
  proof_string("", Prf, Str).

proof_string(Prf, print_error(Prf)).

temp_loc("/var/tmp/temp_goal_file").

line_string(line(Num, Cla, Rul), Str) :-
  number_string(Num, NumStr),
  cla_string(Cla, ClaStr),
  term_string(Rul, RulStr),
  join_string([NumStr, ". ", ClaStr, " [", RulStr, "]"], Str).

lines_string(Lns, Str) :-
  maplist(line_string, Lns, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Str).

linearize_trm(fn(Num), Str) :-
  number_binstr(Num, NumStr),
  join_string(["n", NumStr, "f"], Str).

linearize_trm(app(TrmA, TrmB), Str) :-
  linearize_trm(TrmA, StrA),
  linearize_trm(TrmB, StrB),
  join_string([StrA, StrB, "a"], Str).

linearize_atm(rl(Num), Str) :-
  number_binstr(Num, NumStr),
  join_string(["n", NumStr, "r"], Str).

linearize_atm(app(Atm, Trm), Str) :-
  linearize_atm(Atm, StrA),
  linearize_trm(Trm, StrB),
  join_string([StrA, StrB, "a"], Str).

linearize_atm(eq(TrmA, TrmB), Str) :-
  linearize_trm(TrmA, StrA),
  linearize_trm(TrmB, StrB),
  join_string([StrA, StrB, "q"], Str).

linearize_maps([], "e").

linearize_maps([map(Num, Trm) | Maps], Str) :-
  number_binstr(Num, NumStr),
  linearize_trm(Trm, TrmStr),
  linearize_maps(Maps, SubStr),
  join_string([SubStr, "n", NumStr, TrmStr, "c"], Str).

linearize_prf(asm(Num, Maps), LPrf) :-
  number_binstr(Num, NumStr),
  linearize_maps(Maps, MapsStr),
  join_string(["n", NumStr, MapsStr, "I"], LPrf).

linearize_prf(rsl(PrfA, PrfB), LPrf) :-
  linearize_prf(PrfA, StrA),
  linearize_prf(PrfB, StrB),
  join_string([StrA, StrB, "R"], LPrf).

linearize_prf(rep(PrfA, PrfB), LPrf) :-
  linearize_prf(PrfA, StrA),
  linearize_prf(PrfB, StrB),
  join_string([StrA, StrB, "S"], LPrf).

linearize_prf(rtt(Num, PrfA), LPrf) :-
  number_binstr(Num, NumStr),
  linearize_prf(PrfA, StrA),
  join_string(["n", NumStr, StrA, "T"], LPrf).

linearize_prf(sym(PrfA), LPrf) :-
  linearize_prf(PrfA, StrA),
  join_string([StrA, "Y"], LPrf).

linearize_prf(trv(PrfA), LPrf) :-
  linearize_prf(PrfA, StrA),
  join_string([StrA, "V"], LPrf).

linearize_prf(cnt(PrfA), LPrf) :-
  linearize_prf(PrfA, StrA),
  join_string([StrA, "C"], LPrf).

vcheck(Mat, asm(Num, Cnc)) :-
  nth0(Num, Mat, Cnc).

vcheck(Mat, rsl(PrfA, PrfB, Cnc)) :-
  vcheck(Mat, PrfA),
  vcheck(Mat, PrfB),
  conc(PrfA, [lit(neg, Trm) | CncA]),
  conc(PrfB, [lit(pos, Trm) | CncB]),
  append(CncA, CncB, Cnc).

vcheck(Mat, rtt(Num, PrfA, Cnc)) :-
  vcheck(Mat, PrfA),
  conc(PrfA, CncA),
  rot(Num, CncA, Cnc).

vcheck(Mat, cnt(PrfA, [Lit | Cla])) :-
  vcheck(Mat, PrfA),
  conc(PrfA, [Lit, Lit | Cla]).

vcheck(Mat, sub(Maps, PrfA, Cnc)) :-
  vcheck(Mat, PrfA),
  conc(PrfA, CncA),
  subst_cla(Maps, CncA, Cnc).

main([Argv]) :-
  string_chars(Argv, Chs),
  parse_inp([], Chs, Mat),
  temp_loc(Loc),
  write_goal(Loc, Mat),
  read_proof(Loc, Lns),
  compile(Mat, Lns, Prf),
  compress(Prf, CPrf),
  linearize_prf(CPrf, LPrf),
  string_block(LPrf, Str),
  write(Str).
