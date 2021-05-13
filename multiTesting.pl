%%% Operators for Contracts: +(Choice), *(prefix), ~(output), 0(end), 1(tick)
:-  op(900,xfy, [ + ]).
:-  op(800,xfy, [ * ]).
:-  op(700,fx, [ ~ ]).

%%% n(P,N): N is the set of names in P
n(0, []).
n(1, []).
n(tau * P, As):-  n(P, As).
n(A * P, [A|As]):- A \= tau, n(P, As).
n(P + Q, As):- n(P, APs), n(Q, AQs), union(APs, AQs, As).

%%% Operational Semantics for contracts
%%% red(P,L,Q): P -A-> Q
red(1, tick, 0).
red(L * P, L, P).
red(P + _, L, P1) :- red(P, L, P1).
red(_ + Q, L, Q1) :- red(Q, L, Q1).

%%% Weak reduction
%%% wred(P,A,Q): P =A=> Q
wred(P, [], P).
wred(P, [L|S], Q) :- red(P, L, R), L\=tau, wred(R, S, Q).
wred(P, S, Q) :- red(P, tau, R), wred(R, S, Q).


%%% Set of strings
tr(P, T) :- wred(P, T, _).
str(P, S) :- setof(T, tr(P,T), S).

%%% after(P,T,Qs): Qs are the residuals of P after T
after(P, T, []) :- not(wred(P, T, _)), !.
after(P, T, Qs) :- setof(Q, wred(P,T,Q), Qs).

%%% must(P,L): P MUST L
must([], _).
must([P|Ps], L) :-
    member(X, L), wred(P, [X], _), !, must(Ps, L).

%%% notleqmust(P, Q, S, L): not(P <_must Q) because
%%% (P after S) MUST L but not((Q after S) MUST L)
notleqmust(P, Q, S, L):-
    str(P+Q, Ss), member(S, Ss),
    after(P, S, Ps), after(Q, S, Qs),
    n(P+Q, As), subseteq(L, As),
    must(Ps, L), not(must(Qs, L)).

%%% P <_must Q
leqmust(P,Q) :- not(notleqmust(P,Q,_,_)).

%%% afterC(P,T,Ps): Ps are the residuals of P after the set of traces T
afterC(_,[],[]).
afterC(P,[X|Xs],Ps):- after(P,X,P1s), afterC(P,Xs,P2s), union(P1s,P2s,Ps).

%% afterC(P,T,I,AP) :- str(P,T,I,MS),  dagger(MS,T,I), afterC(P,MS,AP),!.
%% afterC(P,T,I,[]) :- str(P,T,I,MS),  not(dagger(MS,T,I)).

prefs([],_,[]).
prefs([X|Xs],CT,[X|Ys]) :- member(C,CT), append(X,_,C),!,prefs(Xs,CT,Ys),!.
prefs([X|Xs],CT,Ys) :- not((member(C,CT), append(X,_,C))),!, prefs(Xs,CT,Ys).

maximal([],_,[]).
maximal([X|Xs],Y,[X|Zs]) :- not((member(W,Y), append(X,[_|_],W))), !, maximal(Xs,Y,Zs),!.
maximal([X|Xs],Y,Zs) :- member(W,Y), append(X,[_|_],W),!, maximal(Xs,Y,Zs).

maxPrefs(P,T,I,MR) :- independence(I,Ind), mazurkiewicz(Ind,[T],CT),
    str(P,SP), prefs(SP,CT,PSP), maximal(PSP,PSP,MR).%,!.

%% maximalPref(P,T,I,MS) :- independence(I,Ind), mazurkiewicz(Ind,[T],CT), str(P,SP),
%%    prefs(SP,CT,PSP), maximal(PSP,PSP,MS),!.

strClass(P,T,I,MS):-  maxPrefs(P,T,I,MS), dagger(MS,T,I).
strClass(P,T,I,[]):-  maxPrefs(P,T,I,MS), not(dagger(MS,T,I)).

dagger(MS,T,I) :- not((member(Ii,I), filter(T,Ii,TI), not((member(FS,MS),filter(FS,Ii,TI))))).

%%% notlequnc(P,Q,I,T,L): not(P <_unc^I Q) because
%%% (P afterC T) MUST L but not((Q afterC T) MUST L)
notlequnc(P,Q,I,T,L):-
    str(P+Q,Ts), !, member(T,Ts),
    strClass(P,T,I,CTP), strClass(Q,T,I,CTQ),
    afterC(P,CTP,Ps), afterC(Q,CTQ,Qs),
    member(PI, I), subseteq(L, PI),
    must(Ps, L), not(must(Qs,L)).


%%% P<unc^I Q
lequnc(P,Q,I) :- not(notlequnc(P,Q,I,_,_)).

equnc(P,Q,I) :- lequnc(P,Q,I), lequnc(Q,P,I).

%%% notleqind(P,Q,I,T,L): not(P <_ind^I Q) because
%%% (P afterC T) MUST L but not((Q afterC T) MUST L)
notleqind(P,Q,I,T,L1):-
    str(P+Q,Ts), member(T,Ts),
    member(PI,I), filtered(T,PI,Ts,CT), afterC(P,CT,P1), afterC(Q,CT,Q1),
    complement(I, PI, C), subseteq(L1, PI), append(L1,C,L),
    must(P1, L), not(must(Q1,L)).

leqind(P,Q,I) :- not(notleqind(P,Q,I,_,_)).

eqind(P,Q,I) :- leqind(P,Q,I), leqind(Q,P,I).

%%% TESTS: Cassandra

proc(coord,
     get * (  tau * ~err * 0 + tau * ~ret * 0
	    + tau * Query1   + tau * Query2
      	    + tau * Query12  + tau * Query21)) :-
    proc(query(1), Query1), proc(query(2), Query2),
    proc(query(1,2), Query12), proc(query(2,1), Query21).

proc(query(I),
     ~read(I) * (tau * ~err * 0 +  ret(I) * (tau * ~err * 0 + tau * ~ret * 0))).

proc(query(I,J),
     ~read(I) * ~read(J) *
        (tau * ~err * 0
	 + AnsIJ
	 + AnsJI)) :- proc(ans(I,J),AnsIJ), proc(ans(J,I),AnsJI).

proc(ans(I,J),
     ret(I) *
         (  tau * ~ret * 0
	  + tau * ~err * 0
	  + ret(J) * (tau * ~ret * 0 + tau * ~err * 0))).

proc(coord1, get * Query12) :- proc(query(1,2), Query12).

proc(coord2, get * ~read(1) * ~read(2) * (
	tau * ~err * ret(1) * ret(2) * 0 + Wait12 + Wait21))
     :- proc(wait(1,2), Wait12), proc(wait(2,1), Wait21).

proc(coord3, get * ~read(2) * ~read(1) * (
	tau * ~err * ret(1) * ret(2) * 0 + Wait12 + Wait21))
     :- proc(wait(1,2), Wait12), proc(wait(2,1), Wait21).

proc(wait(I,J),
     ret(I) *
         (  tau * ~ret * ret(J) * 0
	  + tau * ~err * ret(J) * 0
	  + ret(J) * (tau * ~ret * 0 + tau * ~err * 0))).

int([[get,~ret,~err], [~read(1),ret(1)],[~read(2),ret(2)]]).

%%% Auxiliary predicates
cartprod(S, L) :- findall(R, cart(S, R), L).

cart([], []).
cart([[A | _] | T], [A | R]) :-
   cart(T, R).

cart([[_ | B] | T], R) :-
   cart([B | T], R).

independence([_],[]).
independence([A,B|X],I):-
      cartprod([A,B],X1), cartprod([B,A],X2),
      append(X1,X2,X3), independence([A|X],Y),
      independence([B|X],Z), append(X3,Y,XY),
      append(XY,Z,I).

subseteq([],_).
subseteq([X|Xs], [_|Ys]):- subseteq([X|Xs],Ys).
subseteq([X|Xs], [X|Ys]):- subseteq(Xs,Ys).

swap(_, X, X).
swap(I, X, Y) :-
      member([A,B], I), append(Z1,X1,X),
      append([A,B],Z2,X1), append([B,A],Z2,Y1),
      append(Z1,Y1,Y).

mazurkiewicz(I,Ks,As):-
      member(X,Ks), swap(I, X, Y),
      not(member(Y,Ks)),!, mazurkiewicz(I,[Y|Ks],As).
mazurkiewicz(_,Ks, Ks).


filter([],_,[]).
filter([X|Xs],L,[X|Ys]) :-
      member(X,L), filter(Xs, L, Ys).
filter([X|Xs],L,Ys) :-
      not(member(X,L)), filter(Xs, L, Ys).

filtered(_,_,[],[]).
filtered(T,I,[X|Xs],[X|Ys]):-
      filter(T,I,FT), filter(X,I,FT),
      filtered(T,I,Xs,Ys).
filtered(T,I,[X|Xs],Ys):-
      filter(T,I,FT), filter(X,I,FX),
      FT \= FX,  filtered(T,I,Xs,Ys).

complement(I,PI,C):- subtract(I,[PI],Rest), flatten(Rest,C).



process(p, ((tau * a * b * 0) + (tau * a * c * 0)) + (tau * b * c * 0)+ (tau * d *   0)).
process(q, ((tau * a * b * c * d * 0) + (tau * a * c * 0)) + (tau * b * c * 0)).
process(q1, a * b * 0).
process(q2, a * c * 0).
process(q3, a * a * 0).

int(ind,[[a],[b],[c],[d]]).

%%%% Example 3.13
process(b0, req * ((tau * ~reqF * 0) + (tau * ~reqH * 0) + (tau * ~reqH * ~reqF * 0))).
process(b1, req * ((tau * ~reqF * 0) + (tau * ~reqH * 0) + (tau * ~reqF * ~reqH * 0))).
process(b2, req * ((tau * ~reqF * 0) + (tau * ~reqH * 0) + (tau * ~reqH * ~reqF * 0)+ (tau * ~reqF * ~reqH * 0))).
int(ex313, [[req],[~reqF],[~reqH]]).

ex313(B0,B1,B2,I) :- process(b0,B0),process(b1,B1),process(b2,B2),int(ex313,I),
        equnc(B0,B1,I), equnc(B1,B2,I), equnc(B0,B2,I).

%%%% Example 3.14
process(p314, ((tau * a * 0) + (tau * b * 0))).
ex314(P,Q,I):- process(p314,P), Q = 0, I = [[a],[b]], lequnc(P,Q,I), not(lequnc(Q,P,I)).

%%%% Example 3.15
process(p315, ((a * b * 0) + (a * 0) + (b * 0))).
process(q315, ((b * a * 0) + (a * 0) + (b * 0))).

process(r315, (a * b * 0)).
process(s315, (b * a * 0)).

ex315a(P,Q,I):- process(p315,P), process(q315,Q), I = [[a],[b]], equnc(P,Q,I).
ex315b(R,S,I):- process(r315,R), process(s315,S), I = [[a],[b]], not(lequnc(R,S,I)), not(lequnc(S,R,I)).

%%%% Example 4.10
ex410(R,S,I):- process(r315,R), process(s315,S), I = [[a],[b]], eqind(R,S,I).
ex313Ind(B0,B1,B2,I) :- process(b0,B0),process(b1,B1),process(b2,B2),int(ex313,I),
        eqind(B0,B1,I), eqind(B1,B2,I), eqind(B0,B2,I).
ex314Ind(P,Q,I):- process(p314,P), Q = 0, I = [[a],[b]], leqind(P,Q,I), not(leqind(Q,P,I)).
ex315aInd(P,Q,I):- process(p315,P), process(q315,Q), I = [[a],[b]], eqind(P,Q,I).

%%%% Example 4.11
process(p411, ((a * c * 0) + (b * d * 0))).
process(q411, ((a * d * 0) + (b * c * 0))).
ex411(P,Q,I):- process(p411,P), process(q411,Q), I = [[a,b],[c,d]], eqind(P,Q,I),
not(lequnc(P,Q,I)), not(lequnc(Q,P,I)).
