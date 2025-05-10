#include "pathfinding.h"
#include "comparisons.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>
#include <math.h>

//////////////////////////////////////////// BUSCA EM PROFUNDIDADE //////////////////////////////////////

int findPathRec(int **adjMatrix, int numNos, int inicio, int fim, Noh **caminho, int *visitados, int *contadorVisitacao)
{
    visitados[inicio] = ++(*contadorVisitacao); // Marca a ordem de visita��o do n� atual

    adicionarNoh(caminho, inicio);

    if (ehIgual(inicio, fim))
    {
        return 1;
    }

    for (int i = 0; ehMenor(i, numNos); i++)
    {
        // Usa visitados para verificar se o n� j� foi visitado
        if (ehIgual(adjMatrix[inicio][i], 1) && ehIgual(visitados[i], 0))
        {
            if (findPathRec(adjMatrix, numNos, i, fim, caminho, visitados, contadorVisitacao))
            {
                return 1;
            }
        }
    }

    removerNoh(caminho, inicio);
    return 0;
}

//////////////////////////////////////////// A* //////////////////////////////////////

int heuristica(int noAtual, int fim, int largura) {
    int xAtual = noAtual % largura, yAtual = noAtual / largura;
    int xFim = fim % largura, yFim = fim / largura;
    return abs(xAtual - xFim) + abs(yAtual - yFim);
}

int findPathAStar(int** adjMatrix, int numNos, int inicio, int fim, Noh** caminho, int* visitados) {
    int* distancias = (int*)malloc(numNos * sizeof(int));
    int* predecessores = (int*)malloc(numNos * sizeof(int));
    int* estimativas = (int*)malloc(numNos * sizeof(int));
    int largura = 20;

    // Inicializa��o
    for (int i = 0; ehMenor(i, numNos); i++) {
        distancias[i] = INT_MAX;
        predecessores[i] = -1;
        estimativas[i] = INT_MAX;
    }
    distancias[inicio] = 0;
    estimativas[inicio] = heuristica(inicio, fim, largura);

    for (int i = 0; ehMenor(i, numNos - 1); i++) {
        int atual = -1, minimo = INT_MAX;

        // Encontra o n� com a menor estimativa
        for (int j = 0; ehMenor(j, numNos); j++) {
            if (ehIgual(visitados[j], 0) && ehMenor(estimativas[j], minimo)) {
                minimo = estimativas[j];
                atual = j;
            }
        }

        if (ehIgual(atual, -1) || ehIgual(atual, fim)) break;
        visitados[atual] = 1;

        // Atualiza as dist�ncias e estimativas dos vizinhos
        for (int vizinho = 0; ehMenor(vizinho, numNos); vizinho++) {
            if (ehDiferente(adjMatrix[atual][vizinho], 0) && ehIgual(visitados[vizinho], 0)) {
                int novaDist = distancias[atual] + adjMatrix[atual][vizinho];
                if (ehMenor(novaDist, distancias[vizinho])) {
                    distancias[vizinho] = novaDist;
                    predecessores[vizinho] = atual;
                    estimativas[vizinho] = distancias[vizinho] + heuristica(vizinho, fim, largura);
                }
            }
        }
    }

    // Verifica se encontrou o caminho
    if (ehIgual(distancias[fim], INT_MAX)) {
        free(distancias);
        free(predecessores);
        free(estimativas);
        return 0; // N�o encontrou o caminho
    }

    // Reconstr�i o caminho
    int no = fim;
    while (ehDiferente(no, -1)) {
        adicionarNoh(caminho, no);
        no = predecessores[no];
    }

    free(distancias);
    free(predecessores);
    free(estimativas);
    return 1; // Encontrou o caminho
}

//////////////////////////////////////////// DIJKSTRA //////////////////////////////////////

int findPathDijkstra(int **adjMatrix, int numNos, int inicio, int fim, Noh **caminho, int *visitados, int *contadorVisitacao)
{
    int *d = (int *)malloc(numNos * sizeof(int));             // d(z): distâncias
    int *predecessores = (int *)malloc(numNos * sizeof(int)); // s(z): predecessores
    int *visitacao = (int *)calloc(numNos, sizeof(int));      // Ordem de visitação dos nós

    for (int i = 0; ehMenor(i, numNos); i++)
    {
        d[i] = INT_MAX;
        predecessores[i] = -1;
        visitados[i] = 0;
    }
    d[inicio] = 0;
    *contadorVisitacao = 0;

    while (1)
    {

        int menorDistancia = INT_MAX;
        int atual = -1;

        for (int i = 0; ehMenor(i, numNos); i++)
        {
            if (ehIgual(visitados[i], 0) && ehMenor(d[i], menorDistancia))
            {
                menorDistancia = d[i];
                atual = i;
            }
        }

        if (ehIgual(atual, -1) || ehIgual(atual, fim))
        {
            break;
        }

        visitados[atual] = 1;
        visitacao[atual] = ++(*contadorVisitacao);

        for (int vizinho = 0; ehMenor(vizinho, numNos); vizinho++)
        {
            if (ehMaior(adjMatrix[atual][vizinho], 0) && ehIgual(visitados[vizinho], 0))
            {
                int novaDistancia = d[atual] + adjMatrix[atual][vizinho];
                if (ehMenor(novaDistancia, d[vizinho]))
                {
                    d[vizinho] = novaDistancia;
                    predecessores[vizinho] = atual;
                }
            }
        }
    }

    int noAtual = fim;
    while (ehDiferente(noAtual, -1))
    {
        adicionarNoh(caminho, noAtual);
        noAtual = predecessores[noAtual];
    }

    int distanciaFinal = d[fim];

    free(d);
    free(predecessores);
    free(visitacao);

    return ehIgual(distanciaFinal, INT_MAX) ? 0 : 1;
}

int findPath(int **adjMatrix, int numNos, int inicio, int fim, Noh **caminho, int *visitados)
{
    for (int i = 0; ehMenor(i, numNos); i++)
    {
        visitados[i] = 0;
    }

    return findPathAStar(adjMatrix, numNos, inicio, fim, caminho, visitados);
}

