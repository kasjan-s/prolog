:- ensure_loaded(library(lists)).

:- op(700, xfx, <>).

<>(X, Y) :- X =\= Y.

% notMember(+X, +Lista) - predykat jest prawdziwy, jesli w Lista nie ma elementu X
notMember(_, []) :- !.
notMember(X, [H|T]) :-
  X \= H,
  notMember(X, T).

% Uzywam list jako map. Klucze to indeksy wartosci w liscie.
% Taka reprezentacja wystarczy, jesli wczytany program jest poprawny.
lookupMap(List, Key, Value) :-
  length(List, N),
  Key < N,
  nth0(Key, List, Value).
lookupMap(_, _, 0).

updateMap([], 0, Value, [Value]).
updateMap([_|T], 0, Value, [Value|T]).
updateMap([], Key, Value, [0|T]) :-
  Key > 0,
  NK is Key - 1,
  updateMap([], NK, Value, T).
updateMap([H|T], Key, Value, [H|NT]) :-
  Key > 0,
  NK is Key - 1,
  updateMap(T, NK, Value, NT).

% Inicjalizacja zmiennych
initVars([], []).
initVars([H|T], [(H,0)|NT]) :-
  initVars(T,NT).

% Operacje na zmiennych
lookupVar([(X, Val)|_], X, Val).
lookupVar([_|T], X, Val) :-
  lookupVar(T, X, Val).

updateVar([(X,_)|T], X, Val, [(X, Val)|T]).
updateVar([H|T], X, Val, [H|NT]) :-
  updateVar(T, X, Val, NT).

% Inicjalizacja tablic
initArrays([], []).
initArrays([H|T], [(H,[])|AT]) :-
  initArrays(T, AT). 

% Operacje na tablicach
findArr([(X, Tab)|_], X, Tab).
findArr([_|T], X, Tab) :-
  findArr(T, X, Tab).

updateArr([(X, Map)|T], X, Idx, Val, [(X, MapWy)|T]) :-
  updateMap(Map, Idx, Val, MapWy).
updateArr([H|T], X, Idx, Val, [H|NT]) :-
  updateArr(T, X, Idx, Val, NT).
% Inicjalizacja licznikow rozkazow
initProcs(N, PrList) :-
  length(PrList, N),
  maplist(=(1), PrList).

% Stan programu reprezentuje jako trojke (Var, Arr, PrL), gdzie
%   Var - lista par postaci (x, Val), gdzie Val to wartosc zmiennej x
%   Arr - lista par postaci (array, Vals), gdzie Vals to lista wartosci
%         tablicy array. Trzymam w pamieci tylko elementy z indeksow 0..TOP,
%         gdzie TOP to maksymalny indeks, dla ktorego wywolana zostala
%         instrukcja przypisania assign(arr(array, TOP), _) (do danego
%         momentu wykonania programu)
%   PrL - lista licznikow rozkazow. N-ta pozycja listy to licznik rozkazow
%         N-tego procesora

% initState(+Program, +N, -StanPoczatkowy)
initState((vars(V), arrays(A), program(_)), N, (Vars, Arrs, PrList)) :-
  initVars(V, Vars),
  initArrays(A, Arrs),
  initProcs(N, PrList).

% Prawda, jesli jakies dwa procesy wskazuja na instrukcje sekcja
% Pr1 i Pr2 sa rowne numerom tych procesow
illegalState(program(P), (_, _, PrL), [Pr1, Pr2]) :-
  nth0(Pr1, PrL, CtPr1),
  nth0(Pr2, PrL, CtPr2),
  Pr1 =\= Pr2,
  nth1(CtPr1, P, sekcja),
  nth1(CtPr2, P, sekcja), !.


% Wyliczanie wyrazen
% pid
calculate(pid, (PrId, _, _), PrId) :- !.
% liczby
calculate(N, (_, _, _), N) :-
  number(N), !.
% zmienne tablicowe
calculate(arr(X, Wyr), (PrId, Var, Arr), Val) :-
  atomic(X),
  calculate(Wyr, (PrId, Var, Arr), Idx),
  findArr(Arr, X, Tab),
  lookupMap(Tab, Idx, Val), !.
% zmienne
calculate(X, (_, Var, _), Val) :-
  atomic(X),
  lookupVar(Var, X, Val), !.
% wyrazenia arytmetyczne
calculate(Comp, (PrId, Var, Arr), Val) :-
  functor(Comp, _, 2),
  Comp =.. [Op, Wyr1, Wyr2],
  calculate(Wyr1, (PrId, Var, Arr), Val1),
  calculate(Wyr2, (PrId, Var, Arr), Val2),
  RetComp =.. [Op, Val1, Val2],
  !,
  Val is RetComp.

% przypisywanie wartosci do zmiennych i do tablic
bind(X, Val, _, (Var, Arr), (VarWy, Arr)) :-
  atomic(X),
  updateVar(Var, X, Val, VarWy).
bind(arr(X, Wyr), Val, PrId, (Var, Arr), (Var, ArrWy)) :-
  atomic(X),
  calculate(Wyr, (PrId, Var, Arr), Idx),
  updateArr(Arr, X, Idx, Val, ArrWy).

% wykonywanie instrukcji
execute(sekcja, PrId, CtrPr, (Var, Arr, PrL), (Var, Arr, PrLWy)) :-
  CtrPrWy is CtrPr + 1,
  updateMap(PrL, PrId, CtrPrWy, PrLWy).
execute(goto(N), PrId, _, (Var, Arr, PrL), (Var, Arr, PrLWy)) :-
  number(N),
  updateMap(PrL, PrId, N, PrLWy).
execute(assign(X, Wyr), PrId, CtrPr, (Var, Arr, PrL), (VarWy, ArrWy, PrLWy)) :-
  CtrPtrWy is CtrPr + 1,
  updateMap(PrL, PrId, CtrPtrWy, PrLWy),
  calculate(Wyr, (PrId, Var, Arr), Val),
  bind(X, Val, PrId, (Var, Arr), (VarWy, ArrWy)).
execute(condGoto(WyrL, N), PrId, CtrPr, (Var, Arr, PrL), (Var, Arr, PrLWy)) :-
  number(N),
  functor(WyrL, _, 2),
  WyrL =.. [Op, Wyr1, Wyr2],
  calculate(Wyr1, (PrId, Var, Arr), Val1),
  calculate(Wyr2, (PrId, Var, Arr), Val2),
  RetComp =.. [Op, Val1, Val2],
  call(RetComp) ->
  updateMap(PrL, PrId, N, PrLWy)
  ; CtrPrWy is CtrPr + 1,
  updateMap(PrL, PrId, CtrPrWy, PrLWy).
  

% Zdecydowalem sie na typ - dla PrId. Dzieki temu nie musze pilnowac dla jakich
% procesow szukam ruchu, prolog robi to za mnie. Predykat step jest prawdziwy
% jesli istnieje jakis ruch ze stanu StanWe do stanu StanWy poprzez wykonanie
% instrukcji przez proces PrId.
% step(+Program, +StanWe, -PrId, -StanWy)
step((_, _, program(P)), (Var, Arr, PrL), PrId, (VarWy, ArrWy, PrLWy)) :-
  nth0(PrId, PrL, CtrPr),
  nth1(CtrPr, P, Ins),
  execute(Ins, PrId, CtrPr, (Var, Arr, PrL), (VarWy, ArrWy, PrLWy)).

% Opakowanie na ruch w przeszukiwaniu grafowym
% Trzymam PrId, zeby wiedziec, ktory proces wykonal instrukcje
move(State, Parent, PrId, (State, Parent, PrId)).

% Predykat do generowania mozliwych ruchow ze stanu wejsciowego z pominieciem
% tych, ktore zostaly juz odwiedzone, albo czekaja w kolejce. Nowe stany
% znajduja sie w zmiennej List. Nowe stany
% znajduja sie w zmiennej List.
possibleMoves(Program, StanWe, Queue, Visited, List) :-
  possibleMoves(Program, StanWe, Queue, Visited, [], List).
possibleMoves(Program, StanWe, Queue, Visited, List, NewList) :-
  step(Program, StanWe, PrId, StanWy),
  move(StanWy, _, _, Test),
  notMember(Test, Queue),
  notMember(Test, List),
  notMember((Test,_), Visited) ->
  !,
  possibleMoves(Program, StanWe, Queue, Visited,
                [(StanWy, StanWe, PrId)|List], NewList) ;
  !,
  NewList = List.

% Przeszukiwanie grafu (BFS).
graphSearch(_, [], _, _) :-
  write('Program jest poprawny (bezpieczny).').
graphSearch((_,_,P), [(StanP, Rodzic, PrId)|_], Visited, N) :-
  illegalState(P, StanP, Pr),
  format('Program nie jest poprawny: stan nr ~p nie jest bezpieczny.~n', [N]),
  printPath((StanP, Rodzic, PrId), Visited),
  format('Procesy w sekcji: ~p, ~p.~n', Pr).
graphSearch((V,A,P), [(StanP, Rodzic, PrId)|Tail], Visited, N) :-
  (possibleMoves((V,A,P), StanP, Tail, Visited, StanyWy) ; StanyWy = []),
  append(Tail, StanyWy, NewTail),
  NewVisited = [((StanP, Rodzic, PrId), N)|Visited],
  N1 is N+1,
  dfs((V,A,P), NewTail, NewVisited, N1), !.

% Wypisywanie sciezki (przeplotu)
printPath((_, nil, nil), _) :-
  write('Niepoprawny przeplot'), nl.
printPath((_, Rodzic, PrId), Visited) :-
  move(Rodzic, _, _, ((VR, AR, PRL), RR, PR)),
  member((((VR, AR, PRL), RR, PR), _), Visited),
  printPath(((VR, AR, PRL), RR, PR), Visited),
  nth0(PrId, PRL, Ctr),
  format('   Proces ~p: ~p~n', [PrId, Ctr]).

                                % verify(N, Program)
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
  graphSearch((V,A,P), [(StanP, nil, nil)], [], 0).
verify(_, Program) :-
  format('Error: niepoprawna nazwa pliku - ~p.~n', [Program]).
