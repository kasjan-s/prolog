:- ensure_loaded(library(lists)).

:- op(700, xfx, <>).

<>(X, Y) :- X =\= Y.

init_vars([], []).
init_vars([H|T], [(H,0)|NT]) :-
  init_vars(T,NT).

lookup_map(List, Key, Value) :-
  length(List, N),
  Key < N,
  nth0(Key, List, Value).
lookup_map(_, _, 0).

update_map([], 0, Value, [Value]).
update_map([_|T], 0, Value, [Value|T]).
update_map([], Key, Value, [0|T]) :-
  Key > 0,
  NK is Key - 1,
  update_map([], NK, Value, T).
update_map([H|T], Key, Value, [H|NT]) :-
  Key > 0,
  NK is Key - 1,
  update_map(T, NK, Value, NT).

init_arrays([], []).
init_arrays([H|T], [(H,[])|AT]) :-
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


ruch(Stan, Rodzic, (Stan, Rodzic)).

possibleMoves(Pr, StanWe, Queue, Visited, Lista) :-
  possibleMoves(Pr, StanWe, Queue, Visited, [], Lista).
possibleMoves(Pr, StanWe, Queue, Visited, Lista, NList) :-
  step(Pr, StanWe, _, StanWy),
  ruch(StanWy, _, Test),
  not_member(Test, Queue),
  not_member(Test, Lista),
  not_member((Test,_), Visited) ->
  !,
  possibleMoves(Pr, StanWe, Queue, Visited, [(StanWy, StanWe)|Lista], NList) ;
  !,
  NList = Lista.

dfs(_, [], _, _) :-
  write('Program jest poprawny (bezpieczny).').
dfs((_,_,P), [(StanP, Rodzic)|_], Visited, N) :-
  illegalState(P, StanP),
  format('Program nie jest poprawny: stan nr ~p nie jest bezpieczny.~n', [N]),
  print_path((StanP, Rodzic), Visited).
dfs((V,A,P), [(StanP, Rodzic)|Tail], Visited, N) :-
  (possibleMoves((V,A,P), StanP, Tail, Visited, StanyWy) ; StanyWy = []),
  append(Tail, StanyWy, NewTail),
  NewVisited = [((StanP, Rodzic), N)|Visited],
  N1 is N+1,
  dfs((V,A,P), NewTail, NewVisited, N1), !.


print_path((Stan, nil), _) :-
  write(Stan), nl.
print_path((Stan, Rodzic), Visited) :-
  ruch(Rodzic, _, RuchRodzica),
  member((RuchRodzica, _), Visited),
  print_path(RuchRodzica, Visited),
  write(Stan), nl.
% dfs((V,A,P), [StanP|Tail], Path) :-
%   not_member(StanP, Visited),
%   (possibleMoves((V,A,P), StanP, Tail, StanyWy) ; StanyWy = []),
%   append(Tail, StanyWy, NewTail),
%   dfs((V,A,P), NewTail, [StanP|Path]).
  % step((V,A,P), StanP, PrId, StanWy),
  % append(StanyWy, Seen, NS),
  % remove_dups(NS, NewSeen),
  % member(StanWy, StanyWy),
  % not_member(StanWy, Visited),
  % not_member(StanWy, Seen),
  % dfs((V,A,P), StanWy, [StanP|Path], [StanP|Visited], NewSeen, Aft),
  % .

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
  dfs((V,A,P), [(StanP, nil)], [], 0).
verify(_, Program) :-
  format('Error: niepoprawna nazwa pliku - ~p.~n', [Program]).
                                % verify(N, Program)
                                % initState(+Program, +N, -StanPoczatkowy)
                                % step(+Program, +StanWe, ?PrId, -StanWy)
