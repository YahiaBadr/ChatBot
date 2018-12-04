
%-------------------------------------------------------------
% res(-Sentence)
%-------------------------------------------------------------

res([FirstWord|RestOfSentence]) :-
  reSe([FirstWord|RestOfSentence]).

reSe([FirstWord|RestOfSentence]) :-
  get0(Char),
  readWord(Char,FirstWord,NextChar),
  readRestOfSentence(FirstWord,NextChar,RestOfSentence).

   %--- ancillaries to res -------------------------
   readRestOfSentence(Word,_,[]) :-
     endOfSentenceWord(Word),!.
   readRestOfSentence(_,Char,[NextWord|RestOfSentence]) :-
     readWord(Char,NextWord,NextChar),
     readRestOfSentence(NextWord,NextChar,RestOfSentence).

   readWord(Char,Word,NextChar) :-
     singleCharWord(Char),!,name(Word,[Char]),get0(NextChar).
   readWord(Char,Word,NextChar) :-
     componentChar(Char,NewChar),
     !,
     get0(TempNextChar),
     restWord(TempNextChar,RestWord,NextChar),
     name(Word,[NewChar|RestWord]).
   readWord(_,Word,NextChar) :-
     get0(TempChar),
     readWord(TempChar,Word,NextChar).

   restWord(Char,[NewChar|RestWord],NextChar) :-
     componentChar(Char,NewChar),
     !,
     get0(TempNextChar),
     restWord(TempNextChar,RestWord,NextChar).
     restWord(Char,[],Char).

   singleCharWord(44).  /* , */
   singleCharWord(59).  /* ; */
   singleCharWord(58).  /* : */
   singleCharWord(63).  /* ? */
   singleCharWord(33).  /* ! */
   singleCharWord(46).  /* . */

   componentChar(Char,Char) :- Char>96,Char<123.

   componentChar(Char,L) :- Char>64,Char<91,L is Char+32.

   componentChar(Char,L) :- Char>64,Char<91,L is Char+32.
   componentChar(Char,Char) :- Char>47,Char<58.
   componentChar(39,39).  /* ' */
   componentChar(45,45).  /* - */
   componentChar(95,95).  /* _ */

   endOfSentenceWord('.').
   endOfSentenceWord('!').
   endOfSentenceWord('?').

%-------------------------------------------------------------
% res_pc(-Sentence)
%-------------------------------------------------------------

res_pc([FirstWord|RestOfSentence]) :-
  reSe_pc([FirstWord|RestOfSentence]).

reSe_pc([FirstWord|RestOfSentence]) :-
  get0(Char),
  readWord_pc(Char,FirstWord,NextChar),
  readRestOfSentence_pc(FirstWord,NextChar,RestOfSentence).

   %--- ancillaries to res_pc -------------------------
   readRestOfSentence_pc(Word,_,[]) :-
     endOfSentenceWord(Word),!.
   readRestOfSentence_pc(_,Char,[NextWord|RestOfSentence]) :-
     readWord_pc(Char,NextWord,NextChar),
     readRestOfSentence_pc(NextWord,NextChar,RestOfSentence).

   readWord_pc(Char,Word,NextChar) :-
     singleCharWord(Char),!,name(Word,[Char]),get0(NextChar).
   readWord_pc(Char,Word,NextChar) :-
     componentChar_pc(Char,NewChar),
     !,
     get0(TempNextChar),
     restWord_pc(TempNextChar,RestWord,NextChar),
     name(Word,[NewChar|RestWord]).
   readWord_pc(_,Word,NextChar) :-
     get0(TempChar),
     readWord_pc(TempChar,Word,NextChar).

   restWord_pc(Char,[NewChar|RestWord],NextChar) :-
     componentChar_pc(Char,NewChar),
     !,
     get0(TempNextChar),
     restWord_pc(TempNextChar,RestWord,NextChar).
     restWord_pc(Char,[],Char).

   componentChar_pc(Char,Char) :- Char>96,Char<123.

   componentChar_pc(Char,Char) :- Char>64,Char<91.

   componentChar_pc(Char,L) :- Char>64,Char<91,L is Char+32.
   componentChar_pc(Char,Char) :- Char>47,Char<58.
   componentChar_pc(39,39).  /* ' */
   componentChar_pc(45,45).  /* - */
   componentChar_pc(95,95).  /* _ */

%-------------------------------------------------------------
% ws(+Sentence)
%-------------------------------------------------------------

ws([F|R]) :-
   write(F),
   wrs(R).

   %--- ancillaries to ws ------------------------
   wrs([F|R]) :-
     write(' '),
     write(F),
     wrs(R).
   wrs([]).

%-------------------------------------------------------------
% space/0
%-------------------------------------------------------------

space :- write(' ').

%-------------------------------------------------------------
% rs(-String)
%-------------------------------------------------------------

rs(S) :-
   get0(C),
   (
      C == -1,  S = [], !, fail;
      C == 10,  S = [], ! ;
      C == 32, !, rs(S);
      !, rs(C,S)
   ).

rs(C,[C|Cs]) :-
   get0(D),
   (
      D == -1,  Cs = [], !, fail;
      D == 10,  Cs = [], ! ;
      D == 32,  Cs = [], ! ;
      !, rs(D,Cs)
   ).


%-------------------------------------------------------------
% wrst(+String)
%-------------------------------------------------------------

wrst([]) :- !.
wrst([C|Cs]) :- put(C), wrst(Cs).