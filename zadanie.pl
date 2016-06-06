:- ensure_loaded(library(lists)).

:- op(700, xfx, <>).

<>(X, Y) :- X =\= Y.

init_vars([], []).
init_vars([H|T], [(H,0)|NT]) :-
  init_vars(T,NT).
  
map(nil).
map(node(L, _, _, R)) :- map(L), map(R).
lookup_map(node(_, K, V, _), Key, Value) :-
  K =:= Key,
  !,
  Value is V.
lookup_map(node(L, K, _, _), Key, Value) :-
  Key < K,
  !,
  lookup_map(L, Key, Value).
lookup_map(node(_, K, _, R), Key, Value) :-
  Key > K,
  !,
  lookup_map(R, Key, Value).

update_map(nil, Key, Value, node(nil, Key, Value, nil)).
update_map(node(L, K, _, R), K, Value, node(L, K, Value, R)).
update_map(node(L, K, V, R), Key, Value, node(NewL, K, V, R)) :-
  Key < K,
  !,
  update_map(L, Key, Value, NewL).
update_map(node(L, K, V, R), Key, Value, node(L, K, V, NewR)) :-
  Key > K,
  !,
  update_map(R, Key, Value, NewR).

init_arrays([], []).
init_arrays([H|T], [(H,nil)|AT]) :-
  init_arrays(T, AT). 

init_procs(N, PrList) :-
  length(PrList, N),
  maplist(=(1), PrList).

                                % initState(+Program, +N, -StanPoczatkowy)
initState((vars(V), arrays(A), program(_)), N, (Vars, Arrs, PrList)) :-
  init_vars(V, Vars),
  init_arrays(A, Arrs),
  init_procs(N, PrList).


illegalState(program(P), (_, _, PrL)) :-
  nth0(Pr1, PrL, CtPr1),
  nth0(Pr2, PrL, CtPr2),
  Pr1 =\= Pr2,
  nth1(CtPr1, P, sekcja),
  nth1(CtPr2, P, sekcja),
  !,
  format('Procesy w sekcji: ~p, ~p.~n', [Pr1, Pr2]).

update_list([_|T], 0, Val, [Val|T]).
update_list([H|T], N, Val, [H|NT]) :-
  M is N - 1,
  update_list(T, M, Val, NT).

find_arr([(X, Tab)|_], X, Tab).
find_arr([_|T], X, Tab) :-
  find_arr(T, X, Tab).

update_arr([(X, Map)|T], X, Idx, Val, [(X, MapWy)|T]) :-
  update_map(Map, Idx, Val, MapWy).
update_arr([H|T], X, Idx, Val, [H|NT]) :-
  update_arr(T, X, Idx, Val, NT).

lookup_var([(X, Val)|_], X, Val).
lookup_var([_|T], X, Val) :-
  lookup_var(T, X, Val).

update_var([(X,_)|T], X, Val, [(X, Val)|T]).
update_var([H|T], X, Val, [H|NT]) :-
  update_var(T, X, Val, NT).

oblicz(pid, (PrId, _, _), PrId) :- !.
oblicz(N, (_, _, _), N) :-
  number(N),
  !.
oblicz(arr(X, Wyr), (PrId, Var, Arr), Val) :-
  atomic(X),
  oblicz(Wyr, (PrId, Var, Arr), Idx),
  find_arr(Arr, X, Tab),
  lookup_map(Tab, Idx, Val),
  !.
oblicz(X, (_, Var, _), Val) :-
  atomic(X),
  lookup_var(Var, X, Val),
  !.
oblicz(Comp, (PrId, Var, Arr), Val) :-
  functor(Comp, _, 2),
  Comp =.. [Op, Wyr1, Wyr2],
  oblicz(Wyr1, (PrId, Var, Arr), Val1),
  oblicz(Wyr2, (PrId, Var, Arr), Val2),
  RetComp =.. [Op, Val1, Val2],
  !,
  Val is RetComp.

przypisz(X, Val, _, (Var, Arr), (VarWy, Arr)) :-
  atomic(X),
  update_var(Var, X, Val, VarWy).
przypisz(arr(X, Wyr), Val, PrId, (Var, Arr), (Var, ArrWy)) :-
  atomic(X),
  oblicz(Wyr, (PrId, Var, Arr), Idx),
  update_arr(Arr, X, Idx, Val, ArrWy).

wykonaj(sekcja, PrId, CtrPr, (Var, Arr, PrL), (Var, Arr, PrLWy)) :-
  CtrPrWy is CtrPr + 1,
  update_list(PrL, PrId, CtrPrWy, PrLWy).
wykonaj(goto(N), PrId, _, (Var, Arr, PrL), (Var, Arr, PrLWy)) :-
  number(N),
  update_list(PrL, PrId, N, PrLWy).
wykonaj(assign(X, Wyr), PrId, CtrPr, (Var, Arr, PrL), (VarWy, ArrWy, PrLWy)) :-
  CtrPtrWy is CtrPr + 1,
  update_list(PrL, PrId, CtrPtrWy, PrLWy),
  oblicz(Wyr, (PrId, Var, Arr), Val),
  przypisz(X, Val, PrId, (Var, Arr), (VarWy, ArrWy)).
wykonaj(condGoto(WyrL, N), PrId, CtrPr, (Var, Arr, PrL), (Var, Arr, PrLWy)) :-
  number(N),
  functor(WyrL, _, 2),
  WyrL =.. [Op, Wyr1, Wyr2],
  oblicz(Wyr1, (PrId, Var, Arr), Val1),
  oblicz(Wyr2, (PrId, Var, Arr), Val2),
  RetComp =.. [Op, Val1, Val2],
  call(RetComp) ->
  update_list(PrL, PrId, N, PrLWy)
  ; CtrPrWy is CtrPr + 1,
  update_list(PrL, PrId, CtrPrWy, PrLWy).
  

                                % step(+Program, +StanWe, -PrId, -StanWy)
step((_, _, program(P)), (Var, Arr, PrL), PrId, (VarWy, ArrWy, PrLWy)) :-
  nth0(PrId, PrL, CtrPr),
  nth1(CtrPr, P, Ins),
  wykonaj(Ins, PrId, CtrPr, (Var, Arr, PrL), (VarWy, ArrWy, PrLWy)).

not_member(_, []) :- !.
not_member(X, [H|T]) :-
  X \= H,
  not_member(X, T).

print_list([]).
print_list([H|T]) :-
  write(H), nl,
  print_list(T).

possibleMoves(Pr, StanWe, Lista) :-
  possibleMoves(Pr, StanWe, [], Lista).
possibleMoves(Pr, StanWe, Lista, NList) :-
  step(Pr, StanWe, _, StanWy),
  not_member(StanWy, Lista) ->
  !,
  possibleMoves(Pr, StanWe, [StanWy|Lista], NList) ;
  !,
  NList = Lista.

dfs((V,A,P), StanP, Path, Visited, Seen) :-
  % length(Seen, N),
  % write(N),
  illegalState(P, StanP) ->
  !, print_list([StanP|Path]) ;
  not_member(StanP, Visited),
  possibleMoves((V,A,P), StanP, StanyWy),
  append(StanyWy, Seen, NS),
  remove_dups(NS, NewSeen),
  member(StanWy, StanyWy),
  not_member(StanWy, Visited),
  not_member(StanWy, Seen),
  dfs((V,A,P), StanWy, [StanP|Path], [StanP|Visited], NewSeen).

verify(N, _) :-
  N =< 0,
  format('Error: Niepoprawna wartosc N - ~p.~n', N).
verify(N, Program) :-
  set_prolog_flag(fileerrors, off),
  see(Program),
  !,
  read(V),
  read(A),
  read(P),
  seen,
  initState((V, A, P), N, StanP),
  % possibleMoves((V,A,P), StanP, Lista),
  % print_list(Lista).
  % step((V,A,P), StanP, PrId, StanWy),
  % write(PrId), nl,
  % write(StanWy), nl,
  % 1 =:= 3.
  dfs((V,A,P), StanP, [], [], [StanP]).
verify(_, Program) :-
  format('Error: niepoprawna nazwa pliku - ~p.~n', [Program]).
                                % verify(N, Program)
                                % initState(+Program, +N, -StanPoczatkowy)
                                % step(+Program, +StanWe, ?PrId, -StanWy)
