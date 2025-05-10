#include <SDL2/SDL.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "comparisons.h"
#include "pathfinding.h"

#define MAX_SIZE 100 // Define o tamanho m�ximo permitido para o labirinto
#define WINDOW_WIDTH 600
#define WINDOW_HEIGHT 600

int size = 20; // Tamanho do labirinto (20x20)
int CELL_SIZE;

enum { EMPTY, WALL, START, END, PATH };

int** maze = NULL;
int** path = NULL;
int** pathOrdenado = NULL;
int** adjMatrix = NULL;
Point start = {-1, -1}, end = {-1, -1};

// Fun��o para desenhar o labirinto e o caminho
void drawMaze(SDL_Renderer *renderer, int animouCaminho, int* visitados) {
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            SDL_Rect rect = {j * CELL_SIZE, i * CELL_SIZE, CELL_SIZE, CELL_SIZE};

            if (maze[i][j] == WALL) {
                SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255); // Preto
            } else if (path[i][j] == 1 && animouCaminho) {
                // Desenha o caminho encontrado em verde, com prioridade sobre os n�s visitados
                SDL_SetRenderDrawColor(renderer, 0, 255, 0, 255); // Verde
            } else if (visitados[i * size + j] > 0 && animouCaminho) {
                // Desenha os n�s visitados em laranja, se n�o forem parte do caminho
                SDL_SetRenderDrawColor(renderer, 255, 165, 0, 255); // Laranja
            } else if ((i == start.y && j == start.x)) {
                SDL_SetRenderDrawColor(renderer, 0, 0, 255, 255); // Azul
            } else if ((i == end.y && j == end.x)) {
                SDL_SetRenderDrawColor(renderer, 255, 0, 0, 255); // Vermelho
            } else {
                SDL_SetRenderDrawColor(renderer, 255, 255, 255, 255); // Branco
            }

            SDL_RenderFillRect(renderer, &rect);
            SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255);
            SDL_RenderDrawRect(renderer, &rect);
        }
    }
}


void drawVisited(SDL_Renderer *renderer, int* visitados, int numNos) {
    int ordemMaxima = 0;

    // Encontra a ordem m�xima de visita��o
    for (int i = 0; i < numNos; i++) {
        if (visitados[i] > ordemMaxima) {
            ordemMaxima = visitados[i];
        }
    }

    // Desenha os n�s na ordem em que foram visitados
    for (int ordem = 1; ordem <= ordemMaxima; ordem++) {
        for (int i = 0; i < numNos; i++) {
            if (visitados[i] == ordem) {
                int x = i % size;
                int y = i / size;

                SDL_Rect rect = {x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE};
                SDL_SetRenderDrawColor(renderer, 255, 165, 0, 255); // Laranja
                SDL_RenderFillRect(renderer, &rect);
                SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255);
                SDL_RenderDrawRect(renderer, &rect);
                SDL_RenderPresent(renderer); // Atualiza a tela
                SDL_Delay(50);  // Pausa para a anima��o
            }
        }
    }
}

void drawPath(SDL_Renderer *renderer, int steps) {
    int ordem = steps;
    while (ordem > 0) {
        for (int i = 0; i < size; i++) {
            for (int j = 0; j < size; j++) {
                if (pathOrdenado[i][j] == ordem) {
                    SDL_Rect rect = {j * CELL_SIZE, i * CELL_SIZE, CELL_SIZE, CELL_SIZE};
                    SDL_SetRenderDrawColor(renderer, 0, 0, 255, 255); // Azul
                    SDL_RenderFillRect(renderer, &rect);
                    SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255);
                    SDL_RenderDrawRect(renderer, &rect);
                    SDL_RenderPresent(renderer);
                    SDL_Delay(100);

                    SDL_SetRenderDrawColor(renderer, 0, 255, 0, 255); // Verde
                    SDL_RenderFillRect(renderer, &rect);
                    SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255);
                    SDL_RenderDrawRect(renderer, &rect);
                    SDL_RenderPresent(renderer);
                }
            }
        }
        ordem--;
    }
}

int** createMatrix(int size) {
    int** matrix = malloc(size * sizeof(int*));
    for (int i = 0; i < size; i++) {
        matrix[i] = malloc(size * sizeof(int));
    }
    return matrix;
}

void freeMatrix(int** matrix, int size) {
    for (int i = 0; i < size; i++) {
        free(matrix[i]);
    }
    free(matrix);
}

// Fun��o para salvar o labirinto em um arquivo
void saveMaze() {
    char filename[50];
    printf("Digite o nome do arquivo para salvar (sem extensao .txt): ");
    scanf("%49s", filename); // L� o nome do arquivo do usu�rio
    strcat(filename, ".txt"); // Adiciona a extens�o .txt

    FILE* file = fopen(filename, "w");
    if (!file) {
        printf("Erro ao salvar o labirinto!\n");
        return;
    }

    fprintf(file, "%d\n", size);
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            fprintf(file, "%d ", maze[i][j]);
        }
        fprintf(file, "\n");
    }

    fprintf(file, "%d %d\n", start.x, start.y);
    fprintf(file, "%d %d\n", end.x, end.y);

    fclose(file);
    printf("Labirinto salvo com sucesso como %s!\n", filename);
}

// Fun��o para carregar o labirinto de um arquivo
void loadMaze() {
    char filename[50];
    printf("Digite o nome do arquivo para carregar (sem extensao .txt): ");
    scanf("%49s", filename);
    strcat(filename, ".txt");

    FILE* file = fopen(filename, "r");
    if (!file) {
        printf("Erro ao carregar o labirinto!\n");
        return;
    }

    int old_size = size; // Armazena o tamanho antigo
    // Leia o tamanho do labirinto do arquivo
    fscanf(file, "%d", &size);

    // Liberar a mem�ria das matrizes atuais, se necess�rio
    if (maze != NULL) {
        freeMatrix(maze, old_size);
        freeMatrix(path, old_size);
        freeMatrix(pathOrdenado, old_size);
    }
    if (adjMatrix != NULL) {
        freeMatrix(adjMatrix, old_size * old_size);
    }

    // Recalcular CELL_SIZE
    CELL_SIZE = WINDOW_WIDTH / size;

    // Realocar as matrizes com o novo tamanho
    maze = createMatrix(size);
    path = createMatrix(size);
    pathOrdenado = createMatrix(size);

    // Ler o labirinto do arquivo
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            fscanf(file, "%d", &maze[i][j]);
        }
    }

    fscanf(file, "%d %d", &start.x, &start.y);
    fscanf(file, "%d %d", &end.x, &end.y);

    fclose(file);
    printf("Labirinto carregado com sucesso!\n");

    // Recriar adjMatrix com o novo tamanho
    adjMatrix = createMatrix(size * size);
}

void liberarCaminho(Noh* caminho) {
    Noh* atual = caminho;
    while (atual != NULL) {
        Noh* temp = atual;
        atual = atual->proximo;
        free(temp);
    }
}


// Fun��o para resetar o labirinto
void resetMaze() {
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            maze[i][j] = EMPTY;
            path[i][j] = 0;
            pathOrdenado[i][j] = 0;
        }
    }
    start = (Point){-1, -1};
    end = (Point){-1, -1};

}

// Fun��o para resetar o caminho animado
void resetCaminhoAnimado() {
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            pathOrdenado[i][j] = 0;
            path[i][j] = 0;
        }
    }
}


// Fun��o que converte o labirinto para uma matriz de adjac�ncias
void mazeToAdjMatrix(int** maze, int** adjMatrix) {
    // Zera a matriz de adjac�ncias
    for (int i = 0; i < size * size; i++) {
        for (int j = 0; j < size * size; j++) {
            adjMatrix[i][j] = 0;
        }
    }

    // Preenche a matriz de adjac�ncias com base nas conex�es poss�veis no labirinto
    for (int y = 0; y < size; y++) {
        for (int x = 0; x < size; x++) {
            if (maze[y][x] != WALL) { // N�o conecta paredes
                int node = y * size + x;
                if (x + 1 < size && maze[y][x + 1] != WALL) {
                    adjMatrix[node][node + 1] = 1;
                    adjMatrix[node + 1][node] = 1;
                }
                if (y + 1 < size && maze[y + 1][x] != WALL) {
                    adjMatrix[node][node + size] = 1;
                    adjMatrix[node + size][node] = 1;
                }
            }
        }
    }
}



// Fun��o para inverter uma lista encadeada
Noh* inverterLista(Noh* cabeca) {
    Noh* anterior = NULL;
    Noh* atual = cabeca;
    Noh* proximo = NULL;

    while (atual != NULL) {
        proximo = atual->proximo; // Salva o pr�ximo n�
        atual->proximo = anterior; // Inverte o ponteiro
        anterior = atual; // Move o anterior para frente
        atual = proximo; // Move o atual para frente
    }

    return anterior; // Novo cabe�a da lista invertida
}

int estaInvertido(Noh* cabeca, int pontoDePartida) {
    if (cabeca == NULL) {
        return 0; // Lista vazia, n�o est� invertida
    }
    return cabeca->valor != pontoDePartida; // Retorna 1 se estiver invertida, 0 se n�o estiver
}

int main(int argc, char* argv[]) {
    CELL_SIZE = WINDOW_WIDTH / size; // Tamanho de cada c�lula

    SDL_Init(SDL_INIT_VIDEO);
    SDL_Window* window = SDL_CreateWindow("Labirinto", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, WINDOW_WIDTH, WINDOW_HEIGHT, SDL_WINDOW_SHOWN);
    SDL_Renderer* renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED);

    maze = createMatrix(size);
    path = createMatrix(size);
    pathOrdenado = createMatrix(size);
    adjMatrix = createMatrix(size * size);

    int* visitados = malloc(size * size * sizeof(int));  // Aloca o vetor de n�s visitados

    int running = 1;
    SDL_Event e;
    int steps = 0;
    int mazeSolved = 0;
    int animouCaminho = 0;

    resetMaze();

    printf("Instru��es:\n");
    printf("- Clique esquerdo para adicionar/remover obst�culos.\n");
    printf("- Clique direito para definir o ponto de partida e destino.\n");
    printf("- Pressione 'e' para executar o algoritmo de busca.\n");
    printf("- Pressione 'n' para resetar o mapa.\n");
    printf("- Pressione 'l' para carregar um labirinto salvo.\n");
    printf("- Pressione 's' para salvar o labirinto atual.\n");
    printf("- Pressione 'q' para sair.\n");

    while (running) {
        while (SDL_PollEvent(&e)) {
            if (e.type == SDL_QUIT) {
                running = 0;
            } else if (e.type == SDL_MOUSEBUTTONDOWN) {
                resetCaminhoAnimado();
                int x = e.button.x / CELL_SIZE;
                int y = e.button.y / CELL_SIZE;

                if (e.button.button == SDL_BUTTON_LEFT) {
                    if (maze[y][x] == EMPTY) {
                        maze[y][x] = WALL;
                    } else if (maze[y][x] == WALL) {
                        maze[y][x] = EMPTY;
                    }
                } else if (e.button.button == SDL_BUTTON_RIGHT) {
                    if (start.x == -1) {
                        start = (Point){x, y};
                        maze[y][x] = START;
                    } else if (end.x == -1 && (x != start.x || y != start.y)) {
                        end = (Point){x, y};
                        maze[y][x] = END;
                    }
                }
                mazeSolved = 0;
                animouCaminho = 0;
                steps = 0;
                comparisons = 0;
            } else if (e.type == SDL_KEYDOWN) {
                resetCaminhoAnimado();
                int numNos = size * size;
                // Zera o vetor de n�s visitados
                for (int i = 0; i < numNos; i++) {
                    visitados[i] = 0;
                }
                if (e.key.keysym.sym == SDLK_s) {
                    saveMaze();
                } else if (e.key.keysym.sym == SDLK_l) {
                    resetMaze();
                    loadMaze();
                    mazeSolved = 0;
                    steps = 0;
                    comparisons = 0;

                } else if (e.key.keysym.sym == SDLK_e && start.x != -1 && end.x != -1 && !mazeSolved) {
                    mazeToAdjMatrix(maze, adjMatrix);
//                    int numNos = size * size;

                    // Zera o vetor de n�s visitados
                    for (int i = 0; i < numNos; i++) {
                        visitados[i] = 0;
                    }

                    int startIndex = start.y * size + start.x;
                    int endIndex = end.y * size + end.x;

                    Noh* caminho = NULL;
                    resetComparisons();

                    // Executa o algoritmo de busca de caminho
                    if (findPath(adjMatrix, numNos, startIndex, endIndex, &caminho, visitados)) {
                        // Verifica se a lista est� invertida
                        if (estaInvertido(caminho, endIndex)) {
                            caminho = inverterLista(caminho);
                        }

                        // Desenha os n�s visitados na ordem correta
                        drawVisited(renderer, visitados, numNos);

                        // Percorre a lista encadeada e preenche a matriz path
                        Noh* atual = caminho;
                        steps = -1;
                        while (atual != NULL) {
                            int node = atual->valor;
                            path[node / size][node % size] = 1;
                            pathOrdenado[node / size][node % size] = steps + 1;
                            steps++;
                            atual = atual->proximo;
                        }
                        int totalComparisons = getComparisons();
                        printf("Caminho encontrado com %d passos e %d compara��es.\n", steps, totalComparisons);
                        // Desenha o caminho final
                        drawPath(renderer, steps);

                        // Marca que a anima��o foi conclu�da
                        animouCaminho = 1;

                        // Desenha o estado final do labirinto com o caminho preservado
                        drawMaze(renderer, animouCaminho, visitados);

                        SDL_RenderPresent(renderer);

                        mazeSolved = 1;
                    } else {
                        printf("Caminho n�o encontrado.\n");
                    }
                } else if (e.key.keysym.sym == SDLK_n) {
                    // Pedir ao usu�rio para digitar o novo tamanho do labirinto
                    printf("Digite o novo tamanho do labirinto: ");
                    int novoSize;
                    scanf("%d", &novoSize);

                    // Validar o novo tamanho (opcional, mas recomendado)
                    if (novoSize <= 0 || novoSize > MAX_SIZE) {
                        printf("Tamanho inv�lido! Por favor, escolha um tamanho entre 1 e %d.\n", MAX_SIZE);
                        continue; // Volta ao loop principal sem fazer altera��es
                    }

                    // Liberar as matrizes antigas
                    freeMatrix(maze, size);
                    freeMatrix(path, size);
                    freeMatrix(pathOrdenado, size);
                    freeMatrix(adjMatrix, size * size);
                    free(visitados);

                    // Atualizar o tamanho e recalcular CELL_SIZE
                    size = novoSize;
                    CELL_SIZE = WINDOW_WIDTH / size;

                    // Realocar as matrizes com o novo tamanho
                    maze = createMatrix(size);
                    path = createMatrix(size);
                    pathOrdenado = createMatrix(size);
                    adjMatrix = createMatrix(size * size);
                    visitados = malloc(size * size * sizeof(int));  // Realoca o vetor de n�s visitados

                    // Resetar o labirinto e outras vari�veis
                    resetMaze();
                    steps = 0;
                    mazeSolved = 0;
                    animouCaminho = 0;
                    resetComparisons();

                } else if (e.key.keysym.sym == SDLK_q) {
                    running = 0;
                }
            }
        }

        SDL_SetRenderDrawColor(renderer, 255, 255, 255, 255);
        SDL_RenderClear(renderer);

        drawMaze(renderer, animouCaminho, visitados);
        SDL_RenderPresent(renderer);
    }

    // Libera a mem�ria alocada
    free(visitados);
    freeMatrix(maze, size);
    freeMatrix(path, size);
    freeMatrix(pathOrdenado, size);
    freeMatrix(adjMatrix, size * size);

    SDL_DestroyRenderer(renderer);
    SDL_DestroyWindow(window);
    SDL_Quit();

    return 0;
}
//My Horny Kitty
