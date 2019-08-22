:- [misc].

comma(StrA, StrB, Str) :-
  join_string([StrB, ", ", StrA], Str).

unpack(app(X, Y), Hd, Args) :- 
  unpack(X, Hd, Tmp),
  append(Tmp, [Y], Args).

unpack(X, X, []).

tptp_tuple([], ""). 

tptp_tuple([Hd | Tl], Str) :-
  foldl(comma, Tl, Hd, Tmp),
  join_string(["(", Tmp, ")"], Str).

tptp_trm(var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

tptp_trm(Trm, Str) :-
  unpack(Trm, fn(Num), Args),
  number_string(Num, NumStr),
  maplist(tptp_trm, Args, ArgStrs),
  tptp_tuple(ArgStrs, ArgsStr),
  join_string(["f", NumStr, ArgsStr], Str).

tptp_atm(eq(TrmA, TrmB), Str) :-
  tptp_trm(TrmA, StrA),
  tptp_trm(TrmB, StrB),
  join_string(["(", StrA, " = ", StrB, ")"], Str).

tptp_atm(Atm, Str) :-
  unpack(Atm, rl(Num), Args),
  number_string(Num, NumStr),
  maplist(tptp_trm, Args, ArgStrs),
  tptp_tuple(ArgStrs, ArgsStr),
  join_string(["r", NumStr, ArgsStr], Str).

tptp_lit(lit(neg, Atm), Str) :-
  tptp_atm(Atm, Tmp),
  string_concat("~ " , Tmp, Str).

tptp_lit(lit(pos, Atm), Str) :-
  tptp_atm(Atm, Str).

tptp_cla(Cla, Idx, Str) :-
  number_string(Idx, IdxStr),
  maplist(tptp_lit, Cla, Tmp),
  join_string(Tmp, " | ", Bdy),
  join_string(["cnf(c", IdxStr,
    ", negated_conjecture, (", Bdy, "))."], Str).

tptp_mat([Cla], Idx, Str) :-
  tptp_cla(Cla, Idx, Str).

tptp_mat([Cla | Mat], Idx, Str) :-
  tptp_cla(Cla, Idx, ClaStr),
  NewIdx is Idx + 1,
  tptp_mat(Mat, NewIdx, MatStr),
  join_string([ClaStr, " ", MatStr], Str).

write_goal(Loc, Mat) :-
  tptp_mat(Mat, 1, Goal),
  open(Loc, write, Stream),
  write(Stream, Goal),
  close(Stream).