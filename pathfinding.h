#ifndef PATHFINDING_H
#define PATHFINDING_H

#include "SDL2/SDL.h"
#include "linked_list.h" // Inclusão da lista encadeada

//#define SIZE 50 // Tamanho do labirinto (20x20)

//#define SIZE 50 // Tamanho do labirinto (20x20)
//#define CELL_SIZE 30

//#define SIZE 50
//#define CELL_SIZE 20



typedef struct {
    int x, y;
} Point;

/**
 * Função: findPath
 * ----------------
 * Encontra o caminho mínimo entre o nó de partida e o nó de destino em um grafo representado por uma matriz de adjacências.
 *
 * Parâmetros:
 *   int** adjMatrix   - Matriz de adjacência quadrada que representa o grafo (labirinto).
 *   int numNos        - Número total de nós no grafo.
 *   int inicio        - Índice do nó de partida.
 *   int fim           - Índice do nó de destino.
 *   Noh** caminho     - Ponteiro para uma lista encadeada que armazenará o caminho encontrado.
 *   int* visitados    - Vetor que armazena a ordem de visitação dos nós durante a execução do algoritmo.
 *
 * Retorno:
 *   Retorna 1 se um caminho foi encontrado, 0 caso contrário.
 */
int findPath(int** adjMatrix, int numNos, int inicio, int fim, Noh** caminho, int* visitados);


#endif // PATHFINDING_H

