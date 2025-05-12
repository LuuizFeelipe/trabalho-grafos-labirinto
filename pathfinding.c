#include "pathfinding.h"
#include "comparisons.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>
#include <math.h>


//GRUPO: Luiz Felipe, Amanda Kher e Richer 

// BUSCA EM PROFUNDIDADE --------------------------------------------------------------------------------

int findPathRec(int **matrizAdj, int totalNos, int origem, int destino, Noh **trajeto, int *statusVisita, int *contador)
{
    statusVisita[origem] = ++(*contador);  // Marca o nó como visitado com ordem de visita
    adicionarNoh(trajeto, origem);         // Adiciona o nó atual ao trajeto

    if (ehIgual(origem, destino)) return 1; // Caso base: destino alcançado

    for (int viz = 0; ehMenor(viz, totalNos); viz++) {
        // Verifica se há conexão e se o vizinho ainda não foi visitado
        if (ehIgual(matrizAdj[origem][viz], 1) && ehIgual(statusVisita[viz], 0)) {
            if (findPathRec(matrizAdj, totalNos, viz, destino, trajeto, statusVisita, contador)) return 1;
        }
    }

    removerNoh(trajeto, origem); // Backtracking: remove o nó se não for parte da solução
    return 0;
}

// A* -----------------------------------------------------------------------------------------------------

int calcularHeuristica(int atual, int alvo, int larguraMapa) {
    // Distância de Manhattan como heurística
    int xAtual = atual % larguraMapa, yAtual = atual / larguraMapa;
    int xAlvo = alvo % larguraMapa, yAlvo = alvo / larguraMapa;
    return abs(xAtual - xAlvo) + abs(yAtual - yAlvo);
}

int findPathAEstrela(int **matrizAdj, int totalNos, int origem, int destino, Noh **trajeto, int *statusVisita) {
    int *distancia = (int *)malloc(totalNos * sizeof(int));   // Distância acumulada desde a origem
    int *anterior = (int *)malloc(totalNos * sizeof(int));    // Armazena o nó anterior no caminho
    int *estimativa = (int *)malloc(totalNos * sizeof(int));  // Estimativa total (g + h)
    int larguraMapa = 20; //assume grid 20xN 

    for (int i = 0; ehMenor(i, totalNos); i++) {
        distancia[i] = INT_MAX;
        anterior[i] = -1;
        estimativa[i] = INT_MAX;
    }

    distancia[origem] = 0;
    estimativa[origem] = calcularHeuristica(origem, destino, larguraMapa);

    for (int i = 0; ehMenor(i, totalNos - 1); i++) {
        int menorEst = INT_MAX, noAtual = -1;

        // Seleciona o nó com menor estimativa total que ainda não foi visitado
        for (int j = 0; ehMenor(j, totalNos); j++) {
            if (ehIgual(statusVisita[j], 0) && ehMenor(estimativa[j], menorEst)) {
                menorEst = estimativa[j];
                noAtual = j;
            }
        }

        if (ehIgual(noAtual, -1) || ehIgual(noAtual, destino)) break;
        statusVisita[noAtual] = 1;

        // Explora os vizinhos do nó atual
        for (int vizinho = 0; ehMenor(vizinho, totalNos); vizinho++) {
            if (ehDiferente(matrizAdj[noAtual][vizinho], 0) && ehIgual(statusVisita[vizinho], 0)) {
                int novaDist = distancia[noAtual] + matrizAdj[noAtual][vizinho];
                if (ehMenor(novaDist, distancia[vizinho])) {
                    distancia[vizinho] = novaDist;
                    anterior[vizinho] = noAtual;
                    estimativa[vizinho] = novaDist + calcularHeuristica(vizinho, destino, larguraMapa);
                }
            }
        }
    }

    if (ehIgual(distancia[destino], INT_MAX)) {
        free(distancia);
        free(anterior);
        free(estimativa);
        return 0; // Caminho não encontrado
    }

    // Reconstrói o caminho do destino até a origem
    int atual = destino;
    while (ehDiferente(atual, -1)) {
        adicionarNoh(trajeto, atual);
        atual = anterior[atual];
    }

    free(distancia);
    free(anterior);
    free(estimativa);
    return 1;
}

// DIJKSTRA -----------------------------------------------------------------------------------------------------

int findPathDijkstra(int **matrizAdj, int totalNos, int origem, int destino, Noh **trajeto, int *statusVisita, int *contador)
{
    int *dist = (int *)malloc(totalNos * sizeof(int));         // Distâncias mínimas desde a origem
    int *anterior = (int *)malloc(totalNos * sizeof(int));     // Armazena predecessores
    int *visitacao = (int *)calloc(totalNos, sizeof(int));     // Marca nós já processados

    for (int i = 0; ehMenor(i, totalNos); i++) {
        dist[i] = INT_MAX;
        anterior[i] = -1;
        statusVisita[i] = 0;
    }

    dist[origem] = 0;
    *contador = 0;

    while (1) {
        int menor = INT_MAX, atual = -1;

        // Seleciona o nó não visitado com menor distância acumulada
        for (int i = 0; ehMenor(i, totalNos); i++) {
            if (ehIgual(statusVisita[i], 0) && ehMenor(dist[i], menor)) {
                menor = dist[i];
                atual = i;
            }
        }

        if (ehIgual(atual, -1) || ehIgual(atual, destino)) break;

        statusVisita[atual] = 1;
        visitacao[atual] = ++(*contador);

        // Atualiza as distâncias dos vizinhos
        for (int viz = 0; ehMenor(viz, totalNos); viz++) {
            if (ehMaior(matrizAdj[atual][viz], 0) && ehIgual(statusVisita[viz], 0)) {
                int novaDist = dist[atual] + matrizAdj[atual][viz];
                if (ehMenor(novaDist, dist[viz])) {
                    dist[viz] = novaDist;
                    anterior[viz] = atual;
                }
            }
        }
    }

    // Reconstrói o caminho
    int atual = destino;
    while (ehDiferente(atual, -1)) {
        adicionarNoh(trajeto, atual);
        atual = anterior[atual];
    }

    int distanciaFinal = dist[destino];

    free(dist);
    free(anterior);
    free(visitacao);

    return ehIgual(distanciaFinal, INT_MAX) ? 0 : 1;
}

// CHAMADA PRINCIPAL -------------------------------------------------------------------------------------

int findPath(int **adjMatrix, int numNos, int inicio, int fim, Noh **caminho, int *visitados)
{
    for (int i = 0; ehMenor(i, numNos); i++) {
        visitados[i] = 0;
    }

    return findPathAEstrela(adjMatrix, numNos, inicio, fim, caminho, visitados); // Usa A* como padrão
}
