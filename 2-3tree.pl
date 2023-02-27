is_node2(node2(_, _, _)).
is_node3(node3(_, _, _, _, _)).
branch(X) :- is_node2(X); is_node3(X).

% greatest(node2(_, _, NR), R) :- branch(NR), greatest(NR, R2), R = R2.
% greatest(node2(I, _, empty), R) :- I = R.
% greatest(node3(_, _, _, _, NR), R) :- branch(NR), greatest(NR, R2), R = R2.
% greatest(node3(_, I, _, _, empty), R) :- I = R.

% lowest(node2(_, NL, _), R) :- branch(NL), lowest(NL, R2), R = R2.
% lowest(node2(I, empty, _), R) :- I = R.
% lowest(node3(_, _, NL, _, _), R) :- branch(NL), lowest(NL, R2), R = R2.
% lowest(node3(_, I, empty, _, _), R) :- I = R.

% is_23tree(empty).
% is_23tree(node2(I, NL, NR)) :- ((branch(NL), lowest(NL, LR), LR < I); NL = empty),
%     ((branch(NR), greatest(NR, RR), RR > I); NR = empty).
% is_23tree(node3(IL, IR, NL, NM, NR)) :- ((branch(NL), lowest(NL, LR), LR < IL); NL = empty),
%     ((branch(NR), greatest(NR, RR), RR > IR); NR = empty),
%     ((branch(NM), lowest(NM, MLR), MLR > IL, greatest(NM, MRR), MRR < IR); NM = empty).

exists(node2(I, _, _), X) :- X = I.
exists(node2(I, branch(NL), _), X) :- X < I, !, exists(NL, X).
exists(node2(I, _, (NL)), X) :- X > I, !, exists(NL, X).

exists(node3(IL, IR, _, _, _), X) :- X = IL, !; X = IR, !.
exists(node3(IL, _, branch(N), _, _), X) :- X < IL, !, exists(X, N).
exists(node3(IL, IR, _ , branch(N), _), X) :- X > IL, X < IR, !, exists(X, N).
exists(node3(_, IR, _, _, branch(N)), X) :- X > IR, !, exists(X, N).

insert_sorted([], V, R) :- R = [V].
insert_sorted([A|N], V, R) :- V < A, R = [V,A|N].
insert_sorted([A|N], V, R) :- V = A, R = [A|N].
insert_sorted([A|N], V, R) :- V > A, insert_sorted(N, V, R2), R = [A|R2].


sort_insert(P, [], P).
sort_insert(P, [A|N], R) :- insert_sorted(P, A, P2), sort_insert(P2, N, R).
sort_insert(P, R) :- sort_insert([], P, R).

was_promoted(promote(V, NL, NR), promote(V, NL, NR)).

insert_node_internal(empty, V, R) :- !, R =  node2(V, empty, empty).
insert_node_internal(node2(IL, empty, empty), V, R) :- !, sort_insert([IL, V], [S1, S2]),
    R = node3(S1, S2, empty, empty, empty).
insert_node_internal(node3(IL, IR, empty, empty, empty), V, R) :- !, sort_insert([IL, IR, V], [S1, S2, S3]),
    R = promote(S2, node2(S1, empty, empty), node2(S3, empty, empty)).

insert_node_internal(node2(I, NL, NR), V, R) :- V < I, !, insert_node_internal(NL, V, R2),
    ((was_promoted(R2, promote(V2, PL, PR)), R = node3(V2, I, PL, PR, NR), !);
    R = node2(I, R2, NR)).
insert_node_internal(node2(I, NL, NR), V, R) :- V > I, !, insert_node_internal(NR, V, R2),
    ((was_promoted(R2, promote(V2, PL, PR)), R = node3(I, V2, NL, PL, PR), !);
    R = node2(I, NL, R2)).

insert_node_internal(node3(IL, IR, NL, NM, NR), V, R) :- V > IR, !, insert_node_internal(NR, V, R2),
    ((was_promoted(R2, promote(V2, PL, PR)), R = promote(IR, node2(IL, NL, NM), node2(V2, PL, PR)));
    R = node3(IL, IR, NL, NM, R2)).
insert_node_internal(node3(IL, IR, NL, NM, NR), V, R) :- V < IL, !, insert_node_internal(NL, V, R2),
    ((was_promoted(R2, promote(V2, PL, PR)), R = promote(IL, node2(V2, PL, PR), node2(IR, NM, NR)),  !);
    R = node3(IL, IR, R2, NM, NR)).
insert_node_internal(node3(IL, IR, NL, NM, NR), V, R) :- V > IL, V < IR, !, insert_node_internal(NM, V, R2),
    ((was_promoted(R2, promote(V2, PL, PR)), R = promote(V2, node2(IL, NL, PL), node2(IR, PR, NR)),  !);
    R = node3(IL, IR, NL, R2, NR)).

insert_node(N, V, R) :- insert_node_internal(N, V, R2),
    ((was_promoted(R2, promote(V2, PL, PR)), R = node2(V2, PL, PR));
    R = R2
    ).

insert_all(N, [], N).
insert_all(N, [V | L], R) :- insert_node(N, V, R2), insert_all(R2, L, R), !.


% delete_node(+Tree, +Value, -Result)
% Deletes a value from the given 2-3 tree.
delete_node(empty, _, empty).
delete_node(node2(I, empty, empty), I, empty).
delete_node(node2(I, NL, NR), V, R) :-
    V < I,
    delete_node(NL, V, NL2),
    merge2(I, NL2, NR, R).
delete_node(node2(I, NL, NR), V, R) :-
    V > I,
    delete_node(NR, V, NR2),
    merge2(I, NL, NR2, R).
delete_node(node3(IL, IR, empty, empty, empty), V, R) :-
    (V = IL; V = IR),
    R = node2(IL, empty, empty).
delete_node(node3(IL, IR, NL, empty, NR), V, R) :-
    V < IL,
    delete_node(NL, V, NL2),
    merge3(IL, IR, NL2, empty, NR, R).
delete_node(node3(IL, IR, NL, empty, NR), V, R) :-
    V = IL,
    merge2(IR, NL, NR, R).
delete_node(node3(IL, IR, NL, empty, NR), V, R) :-
    V > IL,
    V < IR,
    delete_node(NR, V, NR2),
    merge3(IL, IR, NL, empty, NR2, R).
delete_node(node3(IL, IR, NL, NM, empty), V, R) :-
    V = IR,
    merge2(IL, NL, NM, R).
delete_node(node3(IL, IR, NL, NM, empty), V, R) :-
    V < IR,
    delete_node(NM, V, NM2),
    merge3(IL, IR, NL, NM2, empty, R).
delete_node(node3(IL, IR, empty, NM, NR), V, R) :-
    V = IL,
    merge2(IR, NM, NR, R).
delete_node(node3(IL, IR, empty, NM, NR), V, R) :-
    V > IL,
    V < IR,
    delete_node(NM, V, NM2),
    merge3(IL, IR, empty, NM2, NR, R).
delete_node(node3(IL, IR, NL, NM, NR), V, R) :-
    V = IL,
    merge2(IR, NL, NM, R).
delete_node(node3(IL, IR, NL, NM, NR), V, R) :-
    V = IR,
    merge2(IL, NM, NR, R).
delete_node(node3(IL, IR, NL, NM, NR), V, R) :-
    V < IL,
    delete_node(NL, V, NL2),
    merge3(IL, IR, NL2, NM, NR, R).
delete_node(node3(IL, IR, NL, NM, NR), V, R) :-
    V > IR,
    delete_node(NR, V, NR2),
    merge3(IL, IR, NL, NM, NR2, R).
    
% merge3(+L, +M, +LL, +MM, +RR, -Result)
% Merges three nodes with the given values and children into a single node.
merge3(L, M, LL, MM, RR, Result) :-
    Result = node3(L, M, LL, MM, RR).

% merge2(+I, +L, +R, -Result)
% Merges two nodes with the given values and left and right children into a single node.
merge2(I, L, R, Result) :-
    Result = node2(I, L, R).
