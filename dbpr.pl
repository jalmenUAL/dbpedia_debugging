:-use_module(library(http/http_open)).
:-use_module(library(clpfd)).
:-use_module(library(clpq)).
%:-use_module(library(semweb/rdf11)).
:-use_module(library(semweb/sparql_client)).
:-dynamic num_rule/1.
:-dynamic rule/3.
:-set_prolog_flag(character_escapes,false).

:-rdf_register_prefix(dbr,'http://dbpedia.org/resource/',[force(true)]).
:-rdf_register_prefix(dbo,'http://dbpedia.org/ontology/',[force(true)]).
:-rdf_register_prefix(dbp,'http://dbpedia.org/property/',[force(true)]).
:-rdf_register_prefix(yago,'http://dbpedia.org/class/yago/',[force(true)]).

%cd('/Users/jalmen/Google Drive/Mi unidad/Investigacion/dbpedia-pl').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%EXAMPLE OF CLP ON FINITE DOMAINS

p(Country):-rdf(Country,rdf:type,yago:'WikicatCountriesInEurope'),
		rdf(Country,dbo:currency,dbr:'Euro'),
		rdf(Country,dbo:officialLanguage,dbr:'Italian_language'),
		rdf(Country,dbo:populationTotal,Population),
		Population>=10000000.

%EXAMPLE OF CLP ON REAL NUMBERS

%r(Country):-rdf(Country,rdf:type,yago:'WikicatCountriesInEurope'),
%		rdf(Country,dbo:currency,dbr:'Euro'),
%		rdf(Country,dbo:officialLanguage,dbr:'Italian_language'),
%		rdf(Country,dbo:humanDevelopmentIndex,Human),
%		Human >= 100.

%EXAMPLE OF TWO OUTPUTS

%q(Country,Capital):-rdf(Country,rdf:type,yago:'WikicatCountriesInEurope'),
%		rdf(Country,dbo:currency,dbr:'Euro'),
%		rdf(Country,dbo:capital,Capital),
%		rdf(Country,dbo:officialLanguage,dbr:'Italian_language'),
%		rdf(Country,dbo:populationTotal,Population),
%		Population>=10000000.


%%%%%%%%%%%%%%%%%%%%%%%%%%%AUXILIAR FUNCTIONS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

conjunct_to_list((A,B), L) :-!,	conjunct_to_list(A, L0),
  			conjunct_to_list(B, L1),
  			append(L0, L1, L).
conjunct_to_list(A, [A]).

list_to_conjunct([X],X):-!.
list_to_conjunct([X|L],(X,PL)):-list_to_conjunct(L,PL).

member_select([X|L],X,L).
member_select([X|L],Y,[X|L2]):-member_select(L,Y,L2).

genvars([]).
genvars([_|L]):-genvars(L).

syntactic_member(X,L):-member(Y,L),X==Y,!.

included([],_):-!.
included([X|RX],L):-syntactic_member(X,L),included(RX,L).
     
%%%%%%%%%%%%%%%%%%%%%WEAK RULES GENERATOR%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clause_gen(_):-retractall(num_rule(_)),assert(num_rule(0)),retractall(rule(_,_,_)),fail.
clause_gen(Pred):-genvars(Vars), Q=..[Pred|Vars], clause(Q,C),!, 
			conjunct_to_list(C,LC),
			generate_rule(LC,WC,L),
			list_to_conjunct(WC,CC),
			append(Vars,L,Variables),
			NQ=..[Pred|Variables],
			num_rule(N),M is N+1,retract(num_rule(N)),
			assert(num_rule(M)),assert(rule(M,NQ,CC)),fail.

generate_rule([X],[Y],L):-rdf_weak(X,Y,L).
generate_rule([X|L],[Y|L2],V):-rdf_weak(X,Y,V1),generate_rule(L,L2,V2),append(V1,V2,V).
generate_rule(L,L2,V):-member_select(L,rdf(A,P,C),RR),term_variables(rdf(A,P,C),VarsR),
				rdf_global_id(X:_,P),X\=rdf,X\=rdfs,
				rdfs(RR,Rdfs),
				term_variables(Rdfs,VarsRR),
				included(VarsR,VarsRR),generate_rule(RR,L2,V).

rdfs([],[]):-!.
rdfs([rdf(A,B,C)|L],[rdf(A,B,C)|RL]):-!,rdfs(L,RL).
rdfs([_|L],RL):-rdfs(L,RL).
 


%%%%%%%%%%%%%%%%%%%%%%%%%%%WEAKENING OF RDF AND CONSTRAINTS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rdf_weak(rdf(A,P,C),rdf(A,P,C),[]):-
			rdf_global_id(X:_,P),(X=rdf;X=rdfs),!.
rdf_weak(F,F,[]).
rdf_weak(rdf(A,B,C),rdf(A,B,D),[D]):-ground(C).
rdf_weak(rdf(A,B,C),rdf(D,B,C),[D]):-!,ground(A).
rdf_weak(F,FW,L):-rdf_weak_exp(F,FW,L).

rdf_weak_exp(A,A,[]):-var(A),!.
rdf_weak_exp(B,A,[A]):-atomic(B),ground(B),!.
rdf_weak_exp(F,FW,V):-F=..[Op,A,B],rdf_weak_exp(A,WA,VA),
			rdf_weak_exp(B,WB,VB),
			FW=..[Op,WA,WB],
			append(VA,VB,V).




%%%%%%%%%%%%%%%%%%%%DEBUGGER%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

deb(P,Q):-member(X,P),member(X,Q),write("There is a positive and negative element at the same time"),nl,!.

deb(P,Q):-pos(P,N,Free,Const1), 
	neg(Q,N,Free,Const2),
	append(Const1,Const2,Const),
	rule(N,R,C),
	genvars(Vars),	 
	R=..[_|Vars],
	append(Head,Free,Vars),
	recommended(C,St),
	ansi_format([bold,fg(blue)], '~w', ["RECOMMENDED QUERY...."]),nl,
	list_to_string(Head,HeadS),
	concat("SELECT ",HeadS,Select),
	concat(Select,"WHERE {",Where),
	concat(Where,St,St1),concat(St1,"}",Query),
	ansi_format([bold,fg(black)], '~w', [Query]),nl,
	(Const\=[]->(ansi_format([bold,fg(blue)], '~w', ["RECOMMENDED VALUES...."]),nl,
	term_variables(Const,VC),
	dump2(Const,VC,VC,CC),
	write_constraints(CC),nl);true),!.
deb(_,_):-write("The requested solutions are not possible").

list_to_string([],"").
list_to_string([X|L],S):-list_to_string(L,SL),term_string(X,Xt),concat("?",Xt,Var),concat(Var,' ',XS),concat(XS,SL,S).


%%%%%%%%%%%%%%%PRINT RESULTS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

dump2(_,A,B,C):-dump(A,B,C),C\=[],!.
dump2(Const,_,_,Const).

write_constraints([]):-!.
write_constraints([F|RF]):-F=..[':',clpq,Clp],
				Clp=..['{}',FC],
				FC=..[Op,A,B],
				write_const(A),
				write(Op),
				write_const(B),
				write(" "),
				write_constraints(RF).
write_constraints([F|RF]):-F=..[Op,A,B],
				write_const(A),
				write(Op),
				write_const(B),
				write(" "),
				write_constraints(RF).

write_const(A):-var(A),!,term_string(A,SV),concat("?",SV,SA),write(SA).	
write_const(A):-integer(A),!,write(A).
write_const(A):-FA is float(A),write(FA).


%%%%%%%%%%%%%%%%%CONSTRAINT SOLVER%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


solvep([],[]).
solvep([C|RC],[NC|RNC]):- transp(C,NC),  call(NC), solvep(RC,RNC).
solven([C|_],[NC]):- transn(C,NC),call(NC).
solven([_|RC],RNC):- solven(RC,RNC).

transp(C,NCC):-C=..[Op,A,B],trans_lit(A,LA,TA),trans_lit(B,LB,TB),TA\=real,TB\=real,!,concat('#',Op,OpS),NCC=..[OpS,LA,LB].
transp(C,NCC):-C=..[Op,A,B],trans_lit(A,LA,real),trans_lit(B,LB,_),!,NC=..[Op,LA,LB],NCC=clpq:{NC}.
transp(C,NCC):-C=..[Op,A,B],trans_lit(A,LA,_),trans_lit(B,LB,real),!,NC=..[Op,LA,LB],NCC=clpq:{NC}.
transn(C,NCC):-C=..[Op,A,B],inv(Op,IOp),trans_lit(A,LA,TA),trans_lit(B,LB,TB),TA\=real,TB\=real,!,concat('#',IOp,OpS),NCC=..[OpS,LA,LB].
transn(C,NCC):-C=..[Op,A,B],inv(Op,IOp),trans_lit(A,LA,real),trans_lit(B,LB,_),!,NC=..[IOp,LA,LB],NCC=clpq:{NC}.
transn(C,NCC):-C=..[Op,A,B],inv(Op,IOp),trans_lit(A,LA,_),trans_lit(B,LB,real),NC=..[IOp,LA,LB],NCC=clpq:{NC}.

trans_lit(A,A,var):-var(A),!.
trans_lit(literal(type(_, V)),V,integer):-integer(V),!.
trans_lit(literal(type(_, V)),V,real):-float(V),!.
trans_lit(literal(type(T, V)),VV,integer):-is_integer(T),!,atom_number(V,VV).
trans_lit(literal(type(_, V)),VV,real):-!,atom_number(V,VV).
trans_lit(C,D,integer):-C=..[Agg,A,B],trans_lit(A,LA,integer),trans_lit(B,LB,integer),!,D=..[Agg,LA,LB].
trans_lit(C,D,integer):-C=..[Agg,A,B],trans_lit(A,LA,var),trans_lit(B,LB,integer),!,D=..[Agg,LA,LB].
trans_lit(C,D,integer):-C=..[Agg,A,B],trans_lit(A,LA,integer),trans_lit(B,LB,var),!,D=..[Agg,LA,LB].
trans_lit(C,D,real):-C=..[Agg,A,B],trans_lit(A,LA,_),trans_lit(B,LB,_),D=..[Agg,LA,LB].

inv('>','=<').
inv('<','>=').
inv('=','=\=').
inv('=\=','=').
inv('>=','<').
inv('=<','>').

is_integer('http://www.w3.org/2001/XMLSchema#decimal').
is_integer('http://www.w3.org/2001/XMLSchema#integer').
is_integer('http://www.w3.org/2001/XMLSchema#int').
is_integer('http://www.w3.org/2001/XMLSchema#long').
is_integer('http://www.w3.org/2001/XMLSchema#short').
is_integer('http://www.w3.org/2001/XMLSchema#byte').
is_integer('http://www.w3.org/2001/XMLSchema#unsignedLong').
is_integer('http://www.w3.org/2001/XMLSchema#unsignedInt').
is_integer('http://www.w3.org/2001/XMLSchema#unsignedShort').
is_integer('http://www.w3.org/2001/XMLSchema#unsignedByte').
is_integer('http://www.w3.org/2001/XMLSchema#negativeInteger').
is_integer('http://www.w3.org/2001/XMLSchema#nonNegativeInteger').
is_integer('http://www.w3.org/2001/XMLSchema#positiveInteger').
is_integer('http://www.w3.org/2001/XMLSchema#nonPositiveInteger').


%%%%%%%%%%%%%%%%%%%%EXPECTED AND UNEXPECTED ANSWERS SOLVING%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


pos([],_,_,[]):-!.
pos([F|RF],N,Free,All):-run(F,N,Free,Const1),pos(RF,N,Free,All2),solvep(Const1,All1),append(All1,All2,All).

neg([],_,_,[]):-!.
neg(RF,N,Free,Const):-neg2(RF,N,Free,Const).
neg2([F|_],N,Free,[]):- \+ run(F,N,Free,_).
neg2([F|_],N,Free,All):-run(F,N,Free,Const),solven(Const,All).
neg2([_|RF],N,Free,Const):-neg2(RF,N,Free,Const).
			

%%%%%%%%%%%%%%%%%%%%%%%%%%%RUN WEAK RULES%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run(P,_,_,_):-P=..[Pred|_],clause_gen(Pred),fail.
run(P,N,New,Const):-rule(N,Q,C),	 
			P=..[H|Args],
			Q=..[H|All],
			append(Args,New,All), 
			launched(C,St,Pattern,Const),
			\+ ground(Pattern),
			concat("SELECT * WHERE {",St,St1),concat(St1," }",St2),
			sparql_query(St2,Row,[ host('dbpedia.org'), path('/sparql/')]),
			Row=..[row|LRow],
			term_variables(Pattern,VarsC),
			VarsC=LRow.

run(P,N,New,Const):-rule(N,Q,C),			 
			P=..[H|Args],
			Q=..[H|All],
			append(Args,New,All),
			launched(C,St,Pattern,Const),
			ground(Pattern),		
			concat("ASK WHERE {",St,St1),concat(St1," }",St2),
			sparql_query(St2,Row,[ host('dbpedia.org'), path('/sparql/')]),
			Row = true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%BUILDS THE CALLED SPARQL QUERY%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
launched(C,St,Pattern,Const):-launched_list(C,"",St,Pattern,Const).
launched_list(C,I,O,Pattern,Const):-C=..[',',A,RA],!,
				launched_rdf_string(A,SA,PatternA,ConstA),
				concat(I,SA,IA),
				launched_list(RA,IA,O,PatternRA,ConstRA),
				append(PatternA,PatternRA,Pattern),
				append(ConstA,ConstRA,Const).
launched_list(C,I,IC,Pattern,Const):-launched_rdf_string(C,SC,Pattern,Const),
				concat(I,SC,IC).

launched_rdf_string(rdf(A,B,C),Rdf2,[rdf(A,B,C)],[]):-!,rdfterm_string(A,SA),
						rdfterm_string(B,SB),
						concat(SA,SB,AB),
						rdfterm_string(C,SC),
						concat(AB,SC,Rdf),
						concat(Rdf," . ",Rdf2).
launched_rdf_string(Op,"",[],[Op]).

%%%%%%%%%%%%%%%%%BUILDS THE RECOMMENDED SPARQL QUERY%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


recommended(C,St):-recommended_list(C,"",St).
recommended_list(C,I,O):-C=..[',',A,RA],!,
				recommended_rdf_string(A,SA),
				concat(I,SA,IA),
				recommended_list(RA,IA,O).
recommended_list(C,I,IC):-recommended_rdf_string(C,SC),
				concat(I,SC,IC).

recommended_rdf_string(rdf(A,B,C),Rdf2):-!,rdfterm_string(A,SA),
						concat(SA," ",SSA),
						rec_rdfterm_string(B,SB),
						concat(SSA,SB,AB),
						rec_rdfterm_string(C,SC),
						concat(" ",SC,SSC),
						concat(AB,SSC,Rdf),
						concat(Rdf," . ",Rdf2).
recommended_rdf_string(F,FF):-F=..[Conn,A,B],
						rec_rdfterm_string(A,SA),
						rec_rdfterm_string(B,SB),
						concat("FILTER(",SA,FA),
						concat(FA,Conn,FOp),
						concat(FOp,SB,FB),
						concat(FB,") ",FF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%RDF TERMS TO STRING%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rdfterm_string(A,SA):-var(A),!,term_string(A,SV),concat("?",SV,SA).
rdfterm_string(A,A):-integer(A),!.
rdfterm_string(A,A):-float(A),!.
rdfterm_string(literal(type(_,V)),VV):-!,atom_number(V,VV).
rdfterm_string(A,SA):-concat(" <",A,A1),concat(A1,"> ",SA).	


rec_rdfterm_string(A,SA):-var(A),!,term_string(A,SV),concat("?",SV,SA).
rec_rdfterm_string(A,A):-integer(A),!.
rec_rdfterm_string(A,A):-float(A),!.
rec_rdfterm_string(literal(type(_,V)),VV):-!,atom_number(V,VV).
rec_rdfterm_string(Op,SSOp):-Op=..[F,A,B],!,rec_rdfterm_string(A,SA),
				rec_rdfterm_string(B,SB),
				concat(SA,F,SOp),
				concat(SOp,SB,SSOp).
rec_rdfterm_string(A,Z):-rdf_global_id(X:Y,A),concat(X,':',XC),concat(XC,Y,Z).			
