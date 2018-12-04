% Author:
% Date: 22-Mar-18
:- [info_food].
:- [read_sentence].
:- discontiguous(response/4).
:- discontiguous (getDiffAnswer/5).
meal(M):-
         M=breakfast;
         M=lunch;
         M=dinner.
cal(X):-
        X=1800.

filterProp(R,L):-
                       setof((H,N),prop(H,R,N),L).
isValid(X):-
          (X=[how, many, calories, does, /*A_food_ingredient_or_type*/_, contain]/*,(prop(A_food_ingredient_or_type,contain,_);prop(A_food_ingredient_or_type,is,_))*/);
          (X=[what,does,/*A_food_type*/_,contain]/*,prop(A_food_type,contain,_)*/);
          (X=[can,i,have,/*A_food_type*/_,for,/*A_meal_type*/_]/*,prop(A_food_type,contain,_),meal(A_meal_type)*/);
          (X=[what,is,/*A_food_ingredient*/_]/*,prop(A_food_ingredient,is,_)*/);
          (X=[how, many, calories, do, i, have, left]);
          (X=[what,kind,of,/*A_food_category*/_,does,/*A_food_type*/_,contain]/*,prop(_,is,A_food_category),prop(A_food_type,contain,_)*/);
          (X=[is,/*A_food_ingredient*/_,a,/*A_food_category*/_,in,/*A_food_type*/_]/*,prop(A_food_ingredient,is,_),prop(_,is,A_food_category),prop(A_food_type,contain,_)*/);
          (X=[what,can,i,have,for,/*A_meal_type*/_,that,contains,/*A_food_ingredient*/_]/*,meal(A_meal_type),prop(A_food_ingredient,is,_)*/);
          (X=[i,ate,/*A_food_type,for*/_,for,/*A_meal_type*/_]/*,meal(A_meal_type),prop(A_food_type,contain,_)*/);
          (X=[i,do,not,eat,/*A_food_ingredient*/_]/*,prop(A_food_ingredient,is,_)*/);
          (X=[quit]).
matchFirst(_,[],[]).
matchFirst(T1,[(T1,H1)|T],[H1-1|T2]):-
                                  matchFirst(T1,T,T2).
matchFirst(T1,[(H,H1)|T],[H1-0|T2]):-
                                 T1\=H,matchFirst(T1,T,T2).
matchSecond(_,[],[]).
matchSecond(T1,[(H1,T1)|T],[H1-1|T2]):-
                                  matchSecond(T1,T,T2).
matchSecond(T1,[(H,H1)|T],[H-0|T2]):-
                                 T1\=H1,matchSecond(T1,T,T2).


mergeMatchLists(L,L2,R):-
                               compress(L,L1),compress(L2,L3),mergehelp(L1,L3,R).
mergehelp(ML1,[],ML1):-ML1\=[].
mergehelp([],[],[]).
mergehelp(L,[H-O|T1],[H-O|T2]):-
                               \+memberhelp(H-_,L),
                               mergehelp(L,T1,T2).
mergehelp(L,[H-O|T1],[H-OT|T2]):-
                                     memberhelp(H-_,L),
                                     gethelp(H,L,O1),
                                     OT is O + O1,
                                     removehelp(L,H,L1),
                                     mergehelp(L1,T1,T2).
compress([],[]).
compress([H-O|T],[H-O|T1]):-
                           \+memberhelp(H-_,T),compress(T,T1).
compress([H-O|T],[H-OT|T1]):-
                           memberhelp(H-_,T),compresshelp([H-O|T],T2,H-OT),compress(T2,T1).
compresshelp(L,L,H-0):-
                         \+memberhelp(H-_,L).
compresshelp([H-O|T],L,H-Oc):-
                              compresshelp(T,L,H-OT),
                              Oc is OT+O.
compresshelp([H-O|T],[H-O|L],H1-Oc):-
                             H\=H1,
                             memberhelp(H1-_,T),
                             compresshelp(T,L,H1-Oc).
memberhelp(H-_,[H-_|_]).
memberhelp(H-_,[H1-_|T]):-
                        H\=H1,
                        memberhelp(H-_,T).
gethelp(H,[H-O|_],O).
gethelp(H,[H1-_|T],O):-
                       H\=H1,
                       gethelp(H,T,O).
removehelp([H-_|T],H,T).
removehelp([H-O|T],H1,[H-O|T2]):-
                       H\=H1,
                       removehelp(T,H1,T2).
bestMatches([H-O|T],BL):-
                    setof(N,bestMatcheshelp(T,H-O,N),BL).
bestMatcheshelp([],H-_,H).
bestMatcheshelp([H-O|T],_-O1,BL):-
                                    O>O1,
                                    bestMatcheshelp(T,H-O,BL).
bestMatcheshelp([_-O|T],H1-O1,BL):-
                                    O1>O,
                                    bestMatcheshelp(T,H1-O1,BL).
bestMatcheshelp([H-O|T],H1-O,BL):-
                                    H@>H1,
                                    bestMatcheshelp(T,H1-O,BL);
                                    bestMatcheshelp(T,H-O,BL).
bestMatchesMin([],_,[]).
bestMatchesMin([H-N|T],N,[H|T1]):-
                                    bestMatchesMin(T,N,T1).
bestMatchesMin([_-O|T],N,T1):-
                              O\=N,
                              bestMatchesMin(T,N,T1).
foodCalhelp(F,C):-
              prop(F,contain,C,cal).
foodCal(F,C):-
              foodCalList([F],C).
foodCalList([],0).
foodCalList([H|T],C):-
                      foodCalList(T,C1),
                      ((foodCalhelp(H,C2),C is C2+C1);(helpcal(H,C3),C is C3+C1)).
helpcal(H,C):-
              setof(N,prop(H,contain,N),L),
              helpcal1(L,0,C).
helpcal1([],S,S).
helpcal1([H|T],S,C):-
                     foodCal(H,S1),
                     S2 is S1+S,
                     helpcal1(T,S2,C).
calcCalorieshelp(hack,[],[],X,X).
calcCalorieshelp(F,[],[],X,C):-
                         foodCal(F,S),
                         C is X-S.
calcCalorieshelp(F,[PQ|T],[PR|T1],X,C):-
                                        (PR=["You", can, have,A_food_type, for, _];PQ=[i,ate,A_food_type,for,_]),
                                        foodCal(A_food_type,A),
                                        X1 is X-A,
                                        calcCalorieshelp(F,T,T1,X1,C).
calcCalorieshelp(F,[PQ|T],[PR|T1],X,C):-
                                         PR\=["You", can, have,_ , for, _],
                                         PQ\=[i,ate,_,for,_],
                                        calcCalorieshelp(F,T,T1,X,C).
calcCalories(F,PQ,PR,C):-
                     cal(X),
                     calcCalorieshelp(F,PQ,PR,X,C).
getDiffAnswer(Q,PQ,_,[R|_],R):-
                             \+memberhelp2(Q,PQ).
getDiffAnswer(Q,[Q|T],[[PR]|T1],CR,R):-
                                     removehelp2(PR,CR,CR1),
                                     getDiffAnswer(Q,T,T1,CR1,R).
getDiffAnswer(Q,[Q1|T],[_|T1],CR,R):-
                                      Q\=Q1,
                                      memberhelp2(Q,T),
                                      getDiffAnswer(Q,T,T1,CR,R).
memberhelp2(Q,[Q|_]).
memberhelp2(Q,[Q1|T]):-
                       Q\=Q1,
                       memberhelp2(Q,T).
removehelp2(R,[R|T],T).
removehelp2(R,[R1|T],[R1|T1]):-
                         R\=R1,
                         removehelp2(R,T,T1).
listOrderDesc(L,R):-
                   insertion_sort(L,R).
insertion_sort(List,Sorted):-i_sort(List,[],Sorted).
i_sort([],X,X).
i_sort([H|T],Accumulator,Sorted):- insert(H,Accumulator,N),i_sort(T,N,Sorted).
insert(H-X,[H1-Y|T],[H1-Y|NT]):-X<Y,insert(H-X,T,NT).
insert(H-X,[H1-Y|T],[H-X,H1-Y|T]):-X>=Y.
insert(H-X,[],[H-X]).

foodFromHistory([],[]).
foodFromHistory([[i,ate,A,for,_]|T],[A|T2]):-
                                foodFromHistory(T,T2).
foodFromHistory([[you,can,have,A,for,_]|T],[A|T2]):-
                                foodFromHistory(T,T2).
foodFromHistory([H|T],T2):-
                                H\=[i,ate,_,for,_],H\=[you,can,have,_,for,_],
                                foodFromHistory(T,T2).

%I do not eat fish.
getUnlikedIngredients([],[]).
%getUnlikedIngredients([PQ|T],R):-
%                                  PQ=[i,do,not,eat,A],setof(B,prop(B,contain,A),L),
%                                  getUnlikedIngredients(T,T2),
%                                 append(L,T2,R).
getUnlikedIngredients([PQ|T],[A|T2]):-
                                  PQ=[i,do,not,eat,A],
                                  getUnlikedIngredients(T,T2).
getUnlikedIngredients([PQ|T],T2):-
                                  PQ\=[i,do,not,eat,_],
                                  getUnlikedIngredients(T,T2).

%Responses
response(Q,_,_,["I",do,not,know]) :-
                                  Q = [what,kind,of,FC,does,F,contain],
                                  (\+ prop(_,_,FC);\+prop(F,_,_)).

response(Q,_,_,["Nothing",from,what,i,know]) :-
                                             Q = [what,kind,of,FC,does,F,contain],
                                             setof(B,prop(B,is,FC),TMP),length(TMP,N),N>0,
                                             setof(C,prop(F,contain,C),TMP1),length(TMP1,N1),N1>0,
                                             filterProp(contain,L1),
                                             filterProp(is,L2),
                                             matchFirst(F,L1,R1),
                                             matchSecond(FC,L2,R2),
                                             mergeMatchLists(R1,R2,L3),
                                             bestMatchesMin(L3,2,CR),
                                             length(CR,0).
response(Q,PQ,PR,[R]) :-
                      Q = [what,kind,of,FC,does,F,contain],
                      setof(B,prop(B,is,FC),TMP),length(TMP,Nn),Nn>0,
                      setof(C,prop(F,contain,C),TMP1),length(TMP1,N1),N1>0,
                      filterProp(contain,L1),
                      filterProp(is,L2),
                      matchFirst(F,L1,R1),
                      matchSecond(FC,L2,R2),
                      mergeMatchLists(R1,R2,L3),
                      bestMatchesMin(L3,2,CR),
                      length(CR,N),
                      N >= 1,
                      getDiffAnswer(Q,PQ,PR,CR,R).
response(Q,PQ,PR,["I",told,you,that,before]) :-
                                             Q = [what,kind,of,FC,does,F,contain],
                                             setof(B,prop(B,is,FC),TMP),length(TMP,Nn),Nn>0,
                                             setof(C,prop(F,contain,C),TMP1),length(TMP1,N1),N1>0,
                                             filterProp(contain,L1),
                                             filterProp(is,L2),
                                             matchFirst(F,L1,R1),
                                             matchSecond(FC,L2,R2),
                                             mergeMatchLists(R1,R2,L3),
                                             bestMatchesMin(L3,2,CR),
                                             length(CR,N),
                                             N >= 1,
                                             \+getDiffAnswer(Q,PQ,PR,CR,_).

response(Q,_,_,["I",do,not,know]):-
                                   Q=[how, many, calories, does, A_food_ingredient_or_type, contain],
                                   (\+prop(A_food_ingredient_or_type,is,_),\+prop(A_food_ingredient_or_type,contain,_)).
response(Q,PQ,_,[X,"Calories"]):-
                                 Q=[how, many, calories, does, A_food_ingredient_or_type, contain],
                                 \+memberhelp2(Q,PQ),
                                 (prop(A_food_ingredient_or_type,is,_);(setof(YA,prop(A_food_ingredient_or_type,contain,YA),YAYA),length(YAYA,YO),YO>0)),
                                 foodCal(A_food_ingredient_or_type,X).
response(Q,PQ,_,["I",told,you,that,before]):-
                                 Q=[how, many, calories, does, A_food_ingredient_or_type, contain],
                                 (prop(A_food_ingredient_or_type,is,_);prop(A_food_ingredient_or_type,contain,_)),
                                 memberhelp2(Q,PQ).
response(Q,_,_,["I",do,not,know]):-
                     Q=[what,does,A,contain],
                     \+prop(A,contain,_).
response(Q,PQ,PR,[R]):-
                     Q=[what,does,A,contain],
                     prop(A,contain,R),
                     filterProp(contain,L1),
                     matchFirst(A,L1,LO),
                     bestMatchesMin(LO,1,CR),
                     getDiffAnswer(Q,PQ,PR,CR,R).
response(Q,PQ,PR,["I",told,you,that,before]):-
                     Q=[what,does,A,contain],
                     setof(B,prop(A,contain,B),TMP),
                     length(TMP,N),
                     N>=1,
                     filterProp(contain,L1),
                     matchFirst(A,L1,LO),
                     bestMatchesMin(LO,1,CR),
                     \+getDiffAnswer(Q,PQ,PR,CR,_).
helper_can_i_have(PQ,PR,A):-
                           (prop(A,is,_);prop(A,contain,_)),calcCalories(hack,PQ,PR,_).
response(Q,PQ,PR,["I",do,not,know]):-
                                     Q=[can,i,have,A,for,M],
                                     \+prop(A,not,M),
                                     \+helper_can_i_have(PQ,PR,A).
response([can,i,have,A,for,M],PQ,PR,["You",can ,have ,A ,for,M]):-
                                               prop(A,is,_),meal(M),
                                               \+prop(A,not,M),
                                               calcCalories(A,PQ,PR,C),
                                                 C>=0.
response([can,i,have,A,for,M],PQ,PR,["You",can ,have ,A ,for,M]):-
                                                 setof(B,prop(A,contain,B),TMP),
                                                 length(TMP,N),
                                                 N>=1,
                                                 meal(M),
                                                 calcCalories(A,PQ,PR,C),
                                                 C>=0,
                                                 \+prop(A,not,M).
                                                 %\+memberhelp2([can,i,have,A,for,M],PQ).
%response([can,i,have,A,for,M],PQ,_,["I",told ,you ,that ,before]):-
%                                                 setof(B,prop(A,contain,B),TMP),
%                                                 length(TMP,N),
%                                                 N>=1,
%                                                 meal(M),
%                                                 memberhelp2([can,i,have,A,for,M],PQ).
response([can,i,have,A,for,M],PQ,_,[A,is ,not ,suitable ,for ,M]):-
                                                 setof(B,prop(A,contain,B),TMP),
                                                 length(TMP,N),
                                                 N>=1,
                                                 meal(M),
                                                 prop(A,not,M),
                                                 \+memberhelp2([can,i,have,A,for,M],PQ).
response([can,i,have,A,for,M],PQ,PR,["No"]):-
                                                 setof(B,prop(A,contain,B),TMP),
                                                 length(TMP,N),
                                                 N>=1,
                                                 meal(M),
                                                 \+prop(A,not,M),
                                                 \+memberhelp2([can,i,have,A,for,M],PQ),
                                                 calcCalories(A,PQ,PR,C),
                                                 C<0.
response(Q,_,_,["I",do,not,know]) :-
                                  Q=[what,is,A],
                                  \+prop(A,is,_).
response(Q,PQ,_,[R]):-
                    Q=[what,is,A],
                    prop(A,is,R),
                    \+memberhelp2(Q,PQ).
response(Q,PQ,_,["I",told ,you ,that ,before ]):-
                    Q=[what,is,A],
                    prop(A,is,_),
                    memberhelp2(Q,PQ).
response(Q,PQ,PR,[R,"Calories"]):-
                     Q=[how,many,calories,do,i,have,left],
                     %foodFromHistory(PR,FL),
                     %foodCalList(FL,C),
                     calcCalories(hack,PQ,PR,R).
                     %cal(X),
                    %R is X-C.
response(Q,PQ,PR,["I",do,not,know]):-
                    Q=[how,many,calories,do,i,have,left],
                     foodFromHistory(PQ,L1),
                     foodFromHistory(PR,L2),
                     append(L1,L2,L3),
                     \+foodCalList(L3,_).
response(Q,_,_,["I",do,not,know]):-
                                      Q=[is,FI,a,FC,in,FT],
                                      %\+memberhelp2(Q,PQ),
                                      \+prop(FI,is,_),
                                      \+prop(_,is,FC),
                                      \+prop(FT,contain,_).
response(Q,_,_,["Yes"]):-
                                      Q=[is,FI,a,FC,in,FT],
                                      %\+memberhelp2(Q,PQ),
                                      prop(FI,is,FC),
                                     prop(FT,contain,FI).
help_is_FI_a_FC_in_FT(FI,FC,FT):-
                                 prop(FI,is,FC),prop(FT,contain,FI).
response(Q,_,_,["No"]):-
                                      Q=[is,FI,a,FC,in,FT],
                                      %\+memberhelp2(Q,PQ),
                                      \+help_is_FI_a_FC_in_FT(FI,FC,FT).
helpmeplease([],_,[]).
helpmeplease([H|T],L,[H|CR]):-
                          \+memberhelp2(H,L),
                          helpmeplease(T,L,CR).
helpmeplease([H|T],L,CR):-
                          memberhelp2(H,L),
                          helpmeplease(T,L,CR).
helpmeplease2([],A,A).
helpmeplease2([H|T],A,L):-
                          setof(B,prop(B,contain,H),N),
                          append(A,N,A1),
                          append(A1,[H],A2),
                          helpmeplease2(T,A2,L).
helpmeplease2([H|T],A,L):-
                          \+setof(_,prop(_,contain,H),_),
                          append(A,[H],A1),
                          helpmeplease2(T,A1,L).
response(Q,PQ,PR,[R]):-
                      Q=[what,can,i,have,for,M,that,contains,FI],
                      filterProp(contain,L),
                      matchSecond(FI,L,L1),
                      bestMatchesMin(L1,1,L2),
                      filterProp(not,FT_M),
                      matchSecond(M,FT_M,FT_M1),
                      bestMatchesMin(FT_M1,1,FT_M2),
                      helpmeplease(L2,FT_M2,CR1),
                      getUnlikedIngredients(PQ,U),
                      helpmeplease2(U,[],LK1),
                      helpmeplease2(LK1,[],LK2),
                      helpmeplease(CR1,LK2,CR),
                      length(CR,N),N>=1,
                      %write(L2),write('\n'),
                      %write(U),write('\n'),
                      %write(CR),
                      getDiffAnswer(Q,PQ,PR,CR,R).
response(Q,PQ,PR,["I",told,you,that,before]):-
                      Q=[what,can,i,have,for,M,that,contains,FI],
                      filterProp(contain,L),
                      matchSecond(FI,L,L1),
                      bestMatchesMin(L1,1,L2),
                      filterProp(not,FT_M),
                      matchSecond(M,FT_M,FT_M1),
                      bestMatchesMin(FT_M1,1,FT_M2),
                      helpmeplease(L2,FT_M2,CR1),
                      getUnlikedIngredients(PQ,U),
                      helpmeplease2(U,[],LK),
                      helpmeplease(CR1,LK,CR),
                      length(CR,N),N>=1,
                      \+getDiffAnswer(Q,PQ,PR,CR,_).
                      
response(Q,_,_,["I",do,not,know]):-
                      Q=[what,can,i,have,for,M,that,contains,FI],
                      meal(M),
                      \+prop(FI,is,_),
                      \+prop(FI,contain,_).
response(Q,PQ,_,["Nothing",from,what,i,know]):-
                      Q=[what,can,i,have,for,M,that,contains,FI],
                      filterProp(contain,L),
                      matchSecond(FI,L,L1),
                      bestMatchesMin(L1,1,L2),
                      filterProp(not,FT_M),
                      matchSecond(M,FT_M,FT_M1),
                      bestMatchesMin(FT_M1,1,FT_M2),
                      helpmeplease(L2,FT_M2,CR1),
                      getUnlikedIngredients(PQ,U),
                      helpmeplease2(U,[],LK1),
                      helpmeplease2(LK1,[],LK2),
                      helpmeplease(CR1,LK2,CR),
                      setof(B,prop(B,contain,FI),YAYA),length(YAYA,YA),YA>0,
                      length(CR,0).

 response(Q,_,_,["Ok"]):-
                      Q=[i,ate,_,for,_].

response(Q,_,_,["Ok"]):-
                          Q=[i,do,not,eat,_].
                          
responseO(Q,PQ,PR,L5):-
                      Q=[what,can,i,have,for,M,that,contains,FI],
                      filterProp(contain,L),
                      matchSecond(FI,L,L0),
                      compress(L0,L1),
                      filterProp(not,FT_M),
                      matchSecond(M,FT_M,FT_M1),
                      removehelpocc(FT_M1,_-0,FT_M2),
                      getUnlikedIngredients(PQ,U1),
                      helpmeplease2(U1,[],LK1),
                      helpmeplease2(LK1,[],LK),
                      minusocc(L1,LK,FT_M2,L2),
                      calcCalories(hack,PQ,PR,C),
                      plusocc(L2,FI,C,L3),
                      listOrderDesc(L3,L4),
                      makepos(L4,L5).
%End of Responses
makeposhelp([_-Z],Z).
makeposhelp([_|T],Z):-makeposhelp(T,Z).
makepos(L,L1):-
               makeposhelp(L,Z),
               ((Z<0,Z1 is (-1)*Z,makeposhelp2(L,Z1,L1));
               (Z>=0,L1=L)).
makeposhelp2([],_,[]).
makeposhelp2([H-O|T],Z,[H-O1|T2]):-
                                 O1 is O +Z,
                                 makeposhelp2(T,Z,T2).
plusocc([],_,_,[]).
plusocc([H-O|T],FI,C,[H-O1|T2]):-
                                prop(H,contains,FI),
                                foodCal(H,C1),C1=<C,
                                O1 is O+2,
                                plusocc(T,FI,C,T2).
plusocc([H-O|T],FI,C,[H-O1|T2]):-
                                \+prop(H,contains,FI),
                                foodCal(H,C1),C1=<C,
                                O1 is O+1,
                                plusocc(T,FI,C,T2).
plusocc([H-O|T],FI,C,[H-O1|T2]):-
                                prop(H,contains,FI),
                                foodCal(H,C1),C1>C,
                                O1 is O+1,
                                plusocc(T,FI,C,T2).
plusocc([H-O|T],FI,C,[H-O|T2]):-
                                \+prop(H,contains,FI),
                                foodCal(H,C1),C1>C,
                                plusocc(T,FI,C,T2).

minusocc([],_,_,[]).
minusocc([H-O|T],U,FT,[H-O|T2]):-
                                 \+memberhelp(H-_,FT),
                                 \+memberhelp2(H,U),
                                 minusocc(T,U,FT,T2).
minusocc([H-O|T],U,FT,[H-O1|T2]):-
                                 memberhelp(H-_,FT),
                                 memberhelp2(H,U),
                                 O1 is O-2,
                                 minusocc(T,U,FT,T2).
minusocc([H-O|T],U,FT,[H-O1|T2]):-
                                 \+memberhelp(H-_,FT),
                                 memberhelp2(H,U),
                                 O1 is O-1,
                                 minusocc(T,U,FT,T2).
minusocc([H-O|T],U,FT,[H-O1|T2]):-
                                 memberhelp(H-_,FT),
                                 \+memberhelp2(H,U),
                                 O1 is O-1,
                                 minusocc(T,U,FT,T2).

removehelpocc([],_,[]).
removehelpocc([_-O|T],_-O,L):-removehelpocc(T,_-O,L).
removehelpocc([H-O|T],_-O1,[H-O|L]):-O\=O1, removehelpocc(T,_-O1,L).
accumualator(PQ,Q,PR,R,PQN,PRN):-
                                 append(PQ,[Q],PQN),
                                 append(PR,[R],PRN).
                                 %write(PQN),write('\n'),write(PRN).
helpreport([],[],_,-).
helpreport([Q|_],[R|_],M,F):-
                              (Q=[i,ate,F,for,M];
                              R=["You",can,have,F,for,M]).
helpreport([Q|T],[R|T1],M,F):-
                              Q\=[i,ate,F,for,M],
                              R\=["You",can,have,F,for,M],
                              helpreport(T,T1,M,F).
report(PQ,PR):-
               helpreport(PQ,PR,breakfast,B),helpreport(PQ,PR,lunch,L),helpreport(PQ,PR,dinner,D),
        write('>You had '),write(B),write(' for breakfast\n'),
        write('You had '),write(L),write(' for lunch\n'),
        write('You had '),write(D),write(' for dinner\n'),
        %nl,write(PQ),nl,write(PR),nl,
        write('Bye').
readInputTillQuit:-
                   write('> Welcome to your personal assistant\n'),
                   readInputTillQuit2([],[]).
readInputTillQuit2(PQ,PR):-
                      write('> '),
                      res(Y),append(Q,[_],Y),
                      ((isValid(Q),
                      ((Q\=[quit],response(Q,PQ,PR,R),accumualator(PQ,Q,PR,R,PQN,PRN),write('> '),ws(R),write('\n'),readInputTillQuit2(PQN,PRN));(Q=[quit],report(PQ,PR))));
                      (\+ isValid(Q),write('> I can not understand you\n'), readInputTillQuit2(PQ,PR))).
