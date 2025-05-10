#include <stdlib.h>
#include "linked_list.h"

// Função para criar um novo nó
Noh* criarNoh(int valor) {
    Noh* novo = (Noh*)malloc(sizeof(Noh));
    if (novo) {
        novo->valor = valor;
        novo->proximo = NULL;
    }
    return novo;
}

// Função para adicionar um nó à lista encadeada
void adicionarNoh(Noh** caminho, int valor) {
    Noh* novo = criarNoh(valor);
    if (!novo) return;

    if (*caminho == NULL) {
        *caminho = novo;
    } else {
        Noh* atual = *caminho;
        while (atual->proximo != NULL) {
            atual = atual->proximo;
        }
        atual->proximo = novo;
    }
}

// Função para adicionar um nó no final da lista encadeada
void adicionarNohNoFinal(Noh** caminho, int valor) {
    Noh* novoNoh = malloc(sizeof(Noh));
    novoNoh->valor = valor;
    novoNoh->proximo = NULL;
    if (*caminho == NULL) {
        *caminho = novoNoh;
    } else {
        Noh* atual = *caminho;
        while (atual->proximo != NULL) {
            atual = atual->proximo;
        }
        atual->proximo = novoNoh;
    }
}


// Função para liberar a memória da lista encadeada
void liberarLista(Noh* caminho) {
    while (caminho != NULL) {
        Noh* temp = caminho;
        caminho = caminho->proximo;
        free(temp);
    }
}

void removerNoh(Noh** caminho, int valor) {
    // Se a lista estiver vazia, não há nada para remover
    if (*caminho == NULL) {
        return;
    }

    Noh* atual = *caminho;
    Noh* anterior = NULL;

    // Se o primeiro nó contém o valor, remova-o
    if (atual->valor == valor) {
        *caminho = atual->proximo; // Move a cabeça da lista
        free(atual); // Libera a memória
        return;
    }

    // Percorre a lista até encontrar o valor ou chegar ao fim
    while (atual != NULL && atual->valor != valor) {
        anterior = atual;
        atual = atual->proximo;
    }

    // Se não encontrar o valor, apenas retorne
    if (atual == NULL) {
        return;
    }

    // Remove o nó encontrado
    anterior->proximo = atual->proximo;
    free(atual); // Libera a memória do nó removido
}
