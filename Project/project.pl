% Nome: Guilherme Silva  Numero(ist1):106823
:- use_module(library(clpfd)). % para poder usar transpose/2
:- set_prolog_flag(answer_write_options,[max_depth(0)]). % ver listas completas
:- ['puzzlesAcampar.pl']. % Ficheiro dado. No Mooshak tera mais puzzles.

/*----------------------------------------------------------------------------*/
/*-------------------------------4.1-Consultas--------------------------------*/
/*----------------------------------------------------------------------------*/

/*vizinhanca/2 eh um predicado que eh verdade se Vizinh for uma lista ordenada
de coordenadas unicas e adjacentes ah coordenada recebida, sendo as coordenadas
nas posicoes imediatamente acima/abaixo/ah esquerda/ah direita por esta ordem*/

vizinhanca((NumLi,NumCo),Vizinh):- integer(NumLi), integer(NumCo),
    maplist(encontraVizinAux((NumLi,NumCo)), [    (-1,0),
                                           (0,-1),       (0,1),
                                                  ( 1,0)], Vizinh).

/*vizinhancaAlargada/2 eh um predicado que eh verdade se VizAlarg for uma lista
ordenada de coordenadas unicas e adjacentes mais as nas diagonais da coordenada
recebida ordenado de cima para baixo e da esquerda para a direita*/

vizinhancaAlargada((NumLi,NumCo), VizAlarg):- integer(NumLi), integer(NumCo),
    maplist(encontraVizinAux((NumLi, NumCo)),[(-1,-1),(-1,0),(-1,1),
                                              ( 0,-1),       ( 0,1),
                                              ( 1,-1),( 1,0),( 1,1)], VizAlarg).

/*----------------------------Predicado Auxiliar------------------------------*/

/*encontraVizinAux/3 eh um predicado auxiliar que devolve a coordenada,
(NovaLi,NovaCo), resultante da soma da coordenada recebida, (NumLi, NumCo) com o
vetor (X,Y)
--> Usado nos predicados vizinhanca/2 e vizinhancaAlargada/2*/

encontraVizinAux((NumLi, NumCo), (X, Y), (NovaLi, NovaCo)):-
    NovaLi is NumLi + X, NovaCo is NumCo + Y.

/*----------------------------------------------------------------------------*/

/*todasCelulas/2 eh um predicado que eh verdade se TodasCoord eh uma lista
ordenada de cima para baixo da esquerda para a direita com todas as coordenadas,
sem repeticao, do tabuleiro Tabul*/

todasCelulas(Tabul, TodasCoord):-
    findall(Coord, obtemObjetoAux(Tabul,_, Coord), TodasCoord).

/*todasCelulas/3 eh um predicado que eh verdade se TodasCoord eh uma lista
ordenada de cima para baixo e da esquerda para a direita com todas as
coordenadas, sem repeticao, do tabuleiro Tabul em que existe o objeto Obj
(t-> tenda, a-> arvore, r-> relva, _-> variavel para as posicoes livres)*/

todasCelulas(Tabul,TodasCoord,Obj):-(Obj == a; Obj == r; Obj == t; var(Obj)), !,
    findall(Coord, (obtemObjetoAux(Tabul, PossObj, Coord),
        ( PossObj == Obj; var(Obj), var(PossObj) ) ), TodasCoord).

/*calculaObjectosTabuleiro/4 eh um predicado que eh verdade se Tabul for um
tabuleiro, Obj for o tipo de objeto que se procura, e ObjLin e ObjCol forem
listas com o numero de ocorrencias do objeto por linha e por coluna
respetivamente*/

calculaObjectosTabuleiro(Tabul, ObjLin, ObjCol, Obj):-
    maplist(contaObjAux(Obj), Tabul, ObjLin),
    transpose(Tabul, TranspTabul),
    maplist(contaObjAux(Obj), TranspTabul, ObjCol).

/*----------------------------Predicado Auxiliar------------------------------*/

/*contaObjAux/3 eh um predicado auxiliar que tendo o objeto, Obj, conta a
quantidade de ocorrencias do objeto, NumObj, presente na linha recebida, Linha
--> Usado no predicado calculaObjectosTabuleiro/4*/

contaObjAux(Obj, Linha, NumObj):- findall(Elem, (member(Elem, Linha),
    (Elem == Obj; var(Obj), var(Elem)) ), ObjElems), length(ObjElems, NumObj).

/*----------------------------------------------------------------------------*/

/*celulaVazia/2 eh um predicado que eh verdade se Tabul for um tabuleiro com
relva ou sem nada na coordenada fornecida, (NumLi, NumCo), nao falhando caso a
coordenada nao pertenca ao tabuleiro fornecido*/

celulaVazia(Tabul,(NumLi, NumCo)):- length(Tabul,N), ( NumLi < 1; NumLi > N;
                                                       NumCo > N; NumCo < 1),!.
celulaVazia(Tabul, Coord):- obtemObjetoAux(Tabul, Obj, Coord),
                            (Obj == r; var(Obj)).

/*----------------------------------------------------------------------------*/
/*----------------------4.2-Insercao de tendas e relva------------------------*/
/*----------------------------------------------------------------------------*/

/*insereObjectoCelula/3 eh um predicado que eh verdade se Tabul eh um tabuleiro
e se Coord sao as coordenadas onde queremos inserir o objeto, Obj, que tem que
ser ou uma tenda (t) ou uma relva(r)*/

insereObjectoCelula(Tabul, Obj, Coord):-obtemObjetoAux(Tabul, PossVazio, Coord),
    (Obj == t; Obj == r), (PossVazio = Obj; member(PossVazio,[a,t,r])),!.

/*insereObjectoEntrePosicoes/4 eh um predicado que eh verdade se Tabul for um
tabuleiro e (NumLi,NumCo1) e (NumLi,NumCo2) as coordenadas na linha numero NumLi
entre as quais (inclusive) se pretende colocar a tenda ou a relva*/

insereObjectoEntrePosicoes(Tabul, Obj, (NumLi,NumCo1), (NumLi,NumCo2)):-
    NumCo1 =< NumCo2,
    findall( (NumLi,NumCo), between(NumCo1, NumCo2, NumCo), Coords),
    maplist(insereObjectoCelula(Tabul, Obj), Coords).

/*----------------------------------------------------------------------------*/
/*------------------------------4.3-Estrategias-------------------------------*/
/*----------------------------------------------------------------------------*/

/*relva/1 eh um predicado que eh verdade se recebe um puzzle, (Tabul, TenLi,
TenCo), que coloca relva em todas as linhas/colunas cujo numero
de tendas ja atingiu o numero de tendas possivel nessas linhas/colunas*/

relva((Tabul, TenLi, TenCo)):-
    calculaObjectosTabuleiro(Tabul, AtualTLi, AtualTCo, t),
    colocaSePossivelAux(Tabul,AtualTLi,TenLi,r), % Para ver nas linhas
    transpose(Tabul, TranspTabul),
    colocaSePossivelAux(TranspTabul, AtualTCo, TenCo, r). % Para ver nas colunas

/*inacessiveis/1 eh um predicado que eh verdade se Tabul eh um tabuleiro,
que coloca relva em todas as posicoes inacessiveis do tabuleiro, ou seja,
as posicoes que nao estao na vizinhanca de nenhuma arvore*/

inacessiveis(Tabul):- todasCelulas(Tabul, CoordVazias, _),
    findall(CoordInace, (member(CoordInace, CoordVazias),
        vizinhanca(CoordInace, Vizinh), % Nao pode ter arvores na vizinh de _
        contaObjCoordsAux(Tabul, Vizinh, a, 0)), CoordsInaces),
    maplist(insereObjectoCelula(Tabul,r), CoordsInaces).

/*aproveita/1 eh um predicado que eh verdade se recebe um puzzle, (Tabul, TenLi,
TenCo), que coloca tendas nas linhas e colunas em que o numero de tendas por
colocar eh igual ao numero de posicoes livres*/

aproveita((Tabul, TenLi, TenCo)):-
    calculaObjectosTabuleiro(Tabul, AtualTLi, AtualTCo, t),
    calculaObjectosTabuleiro(Tabul,VazioLi, VazioCo, _),
    maplist(plus, AtualTLi, VazioLi, PossTLi),%Soma para depois ver se eh igual
    maplist(plus, AtualTCo, VazioCo, PossTCo),%ao numero de tendas reais do tab.
    colocaSePossivelAux(Tabul,PossTLi,TenLi,t), transpose(Tabul,TranspTabul),
    colocaSePossivelAux(TranspTabul, PossTCo, TenCo, t).

/*----------------------------Predicado Auxiliar------------------------------*/

/*colocaSePossivelAux/4 eh um predicado auxiliar que vai colocar o objeto, Obj,
nas posicoes livres do tabuleiro, Tabul, em que as linhas a preencher com o
objeto sao os indices das listas (comeca em 1 em vez de 0), quando a lista de
tendas colocadas, ColocTen, e a lista de tendas totais, TotalTen, possuem o
mesma numero de tendas para o mesmo indice
--> Usado nos predicados relva/1 e aproveita/1*/

colocaSePossivelAux(Tabul, ColocadasTen, TotalTen, Obj):- length(Tabul, N),
    findall((IndiceLinha, 1), (nth1(IndiceLinha, ColocadasTen, NumTen),
        nth1(IndiceLinha, TotalTen, NumTen)), CoordSubst1),
    findall((IndiceLinha, N), % Para poder inserir na linha completa
        (member((IndiceLinha,_), CoordSubst1)), CoordSubstN),
    maplist(insereObjectoEntrePosicoes(Tabul, Obj),CoordSubst1, CoordSubstN).

/*----------------------------------------------------------------------------*/

/*limpaVizinhancas/1 eh um predicado que eh verdadeiro se recebe um puzzle,
(Tabul,_,_), que coloca relva nas posicoes livres das vizinhancas alargadas das
tendas do tabuleiro*/

limpaVizinhancas((Tabul,_,_)):- todasCelulas(Tabul, CoordsTendas, t),
    findall(VizCoord, (member(CoordTen, CoordsTendas),
        vizinhancaAlargada(CoordTen, VizAlarg), member(VizCoord, VizAlarg),
        obtemObjetoAux(Tabul,_, VizCoord)), CoordVazias), % Coord vazias a subst
    maplist(insereObjectoCelula(Tabul, r), CoordVazias).

/*unicaHipotese/1 eh um predicado que eh verdadeiro se recebe um puzzle,
(Tabul,_,_), que coloca uma tenda na vizinhanca de arvores que apenas possuem
uma posicao livre e que nao possuem ainda nenhuma tenda nessa vizinhanca*/

unicaHipotese((Tabul,_,_)):- todasCelulas(Tabul, ArvsCoords, a),
    findall(VizCoord, (member(ArvCoord, ArvsCoords),
        vizinhanca(ArvCoord, Vizinh), contaObjCoordsAux(Tabul, Vizinh, t, 0),
        contaObjCoordsAux(Tabul, Vizinh, _, 1), member(VizCoord, Vizinh),
        obtemObjetoAux(Tabul, _, VizCoord)), CoordVazias), % Coord vazias a subt
    maplist(insereObjectoCelula(Tabul, t), CoordVazias).

/*----------------------------Predicados Auxiliares---------------------------*/

/*contaObjCoordsAux/4 eh um predicado auxiliar que tendo o objeto, Obj, um
tabuleiro, Tabul, e uma lista de coordenadas, Coords, vai contar o numero de
ocorrencias do objeto, NumObj, nas coordenadas fornecidas do tabuleiro
--> Usado nos predicados inacessiveis/1 e unicaHipotese/1*/

contaObjCoordsAux(Tabul, Coords, Obj, NumObj):- findall(PossObj,
    (member(Coord, Coords), obtemObjetoAux(Tabul,PossObj,Coord)), ObjsDeCoords),
    contaObjAux(Obj, ObjsDeCoords, NumObj).

/*obtemObjetoAux/3 eh um predicado auxiliar que vai obter o objeto, Obj,
presente na coordenada, (NumLi, NumCo), do tabuleiro, Tabul
--> Usado nos predicados todasCelulas/2, todasCelulas/3, celulaVazia/2,
insereObjectoCelula/3, limpaVizinhancas/1, unicaHipotese/1 e
contaObjCoordsAux/4*/

obtemObjetoAux(Tabul, Obj, (NumLi,NumCo)):- nth1(NumLi, Tabul, Linha),
    nth1(NumCo, Linha, Obj).

/*----------------------------------------------------------------------------*/
/*---------------------------4.4-Tentativa e Erro-----------------------------*/
/*----------------------------------------------------------------------------*/

/*valida/2 eh um predicado que eh verdade se LArv e LTen sao listas contendo
as coordenadas das arvores e  das tendas respetivamente, onde eh avaliado a
existencia da correspondencia de uma unica tenda para cada arvore, nao existindo
a repeticao de nenhuma tenda para arvores diferentes*/

valida(LArv, LTen):- length(LArv,N), length(LTen, N), member(Coord, LTen),
    \+ member(Coord, LArv), %Com o mesmo numero de coord sem partilharem coords
    findall(ConjCrdArvs, (member(CoordTen, LTen), vizinhanca(CoordTen, Vizinh),
        arvoresLigadasAux(Vizinh, LArv, ConjCrdArvs)), TdsLigEmArv),
    umaTendaPorArvoreAux(TdsLigEmArv, N),!.

/*----------------------------Predicados Auxiliares---------------------------*/

/*arvoresLigadasAux/3 eh um predicado auxiliar que ao receber uma lista com
coordenas vizinhas de uma tenda, Vizinh, vai selecionar apenas as coordenadas
que representam uma arvore existente na lista de arvores, LArv, e junta-as numa
outra lista, ConjCArvs
--> Usado no predicado valida/2*/

arvoresLigadasAux(Vizinh, LArv, ConjCArvs):-findall(CoordArv,
        (member(CoordArv, Vizinh), member(CoordArv, LArv)), ConjCArvs),
    ConjCArvs \== []. % A tenda tem que ter pelo menos uma arvore na vizinhanca

/*umaTendaPorArvoreAux/2 eh um predicado auxiliar que compara o numero de
ligacoes com o numero de arvores unicas ligadas as tendas
--> Usado no predicado valida/2*/

umaTendaPorArvoreAux(TdsLigEmArv, NumLig):- %flatten torna numa unica lst de arv
    flatten(TdsLigEmArv, TdsArvConec), sort(TdsArvConec, ArvsConenc),
    length(ArvsConenc, NumLig). % Sort vai remover os elementos repetidos

/*----------------------------------------------------------------------------*/

/*resolve/1 eh um predicaso que eh verdadeiro se Puzzle eh um puzzle e que ao
aplicar o predicado o puzzle fica resolvido */

resolve(Puzzle):- Puzzle = (Tabul,TenLi,TenCo), todasCelulas(Tabul,LArv,a),
    inacessiveis(Tabul), relva(Puzzle), aproveita(Puzzle), relva(Puzzle),
    unicaHipotese(Puzzle), limpaVizinhancas(Puzzle), % relva apos adicio. tendas
    todasCelulas(Tabul, LTen, t), todasCelulas(Tabul, LVaz, _),
    (valida(LArv, LTen), calculaObjectosTabuleiro(Tabul, TenLi, TenCo, t),!;
    member(PossTend, LVaz), insereObjectoCelula(Tabul, t, PossTend),
    resolve(Puzzle)). % vai tentando colocar tenda ate atingir a solucao correta
