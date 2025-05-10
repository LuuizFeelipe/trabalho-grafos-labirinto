#ifndef LINKED_LIST_H
#define LINKED_LIST_H

// Estrutura para um nó da lista encadeada
typedef struct Noh {
    int valor;             // Índice do nó
    struct Noh* proximo;   // Ponteiro para o próximo nó
} Noh;

// Funções para manipular a lista encadeada
Noh* criarNoh(int valor);
void adicionarNoh(Noh** caminho, int valor);
void adicionarNohNoFinal(Noh** caminho, int valor);
void liberarLista(Noh* caminho);
void removerNoh(Noh** caminho, int valor);
#endif // LINKED_LIST_H
