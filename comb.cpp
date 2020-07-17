/*_______________________________________________________________________________________________________
|                                                                                                        |
|                           A Combinatorial Algorithm for the MEWC Problem                               |
|                                                                                                        |
|               Copyright (c) 2018 Seyedmohammadhossein Hosseinian. All rights reserved.                 |
|                                                                                                        |
|________________________________________________________________________________________________________|

***  READ ME  ********************************************************************************************

  (1) Before running the code, define N and GRAPH, e.g.,
      #define N 200
      #define GRAPH "brock200_2.clq"
  (2) The algorithm accepts an initial lower bound through the "InitialSol" parameter

 ***********************************************************************************************************/

#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <Windows.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#define N __
#define GRAPH __
#define InitialSol 0
#define LDA N

using namespace std;

#pragma region "Time Record"

double get_wall_time() {
	LARGE_INTEGER time, freq;
	if (!QueryPerformanceFrequency(&freq)) {
		return 0;
	}
	if (!QueryPerformanceCounter(&time)) {
		return 0;
	}
	return (double)time.QuadPart / freq.QuadPart;
}

double get_cpu_time() {
	FILETIME a, b, c, d;
	if (GetProcessTimes(GetCurrentProcess(), &a, &b, &c, &d) != 0) {
		return
			(double)(d.dwLowDateTime |
			((unsigned long long)d.dwHighDateTime << 32)) * 0.0000001;
	}
	else {
		return 0;
	}
}

#pragma endregion

#pragma region "Initial Sort"

struct node {
	int n;
	int degree;			//degree of the vertex in the subgraph induced by R (changing as R is updated)
	int ex_deg;			//sum of "degree" of the vertices adjacent to this vertex in the subgraph induced by R (See definition of ex_deg(q) in Tomita(2007) page 101)
};

bool degCmp(node const & a, node const & b)
{
	return a.degree > b.degree;
}

bool ex_degCmp(node const & a, node const & b)
{
	return a.ex_deg < b.ex_deg;
}

int* sortV(double** Adj, int & Delta) {
	int* V = new int[N];
	vector<node> R;
	vector<node> Rmin;
	node v;
	int dlt = 0;
	for (int i = 0; i < N; i++) {
		v.n = i;
		v.degree = 0;
		for (int j = 0; j < N; j++) {
			if (Adj[i][j] > 0) {
				v.degree += 1;
			}
		}
		if (v.degree > dlt) {
			dlt = v.degree;
		}
		R.push_back(v);
	}
	Delta = dlt;								//inputs Delta and change its value in the function after calculating the degree of all vertices
	sort(R.begin(), R.end(), degCmp);			//sorts "node"s in R in descending order of "degree"
	int minDeg = (R.end() - 1)->degree;
	vector<node>::iterator itr = R.end() - 1;
	while (itr->degree == minDeg) {
		Rmin.push_back(*itr);
		if (itr == R.begin()) {
			break;
		}
		else {
			itr--;
		}
	}
	node p;										//the "node" with the minimum "ex_deg" among nodes in Rmin
	for (int k = N - 1; k >= 0; k--) {
		if (Rmin.size() == 1) {
			p = Rmin[0];
		}
		else {
			for (vector<node>::iterator itr_1 = Rmin.begin(); itr_1 != Rmin.end(); itr_1++) {
				itr_1->ex_deg = 0;
				for (vector<node>::iterator itr_2 = R.begin(); itr_2 != R.end(); itr_2++) {
					if (Adj[itr_1->n][itr_2->n] > 0) {
						itr_1->ex_deg += itr_2->degree;
					}
				}
			}
			sort(Rmin.begin(), Rmin.end(), ex_degCmp);				//sorts "node"s in Rmin in ascending order of "ex_deg"
			p = Rmin[0];
		}
		V[k] = p.n;
		Rmin.clear();
		vector<node>::iterator itr = R.end() - 1;
		while (itr != R.begin()) {
			if (itr->n == p.n) {
				itr = R.erase(itr);
				break;
			}
			else {
				itr--;
			}
		}
		for (vector<node>::iterator itr_1 = R.begin(); itr_1 != R.end(); itr_1++) {
			if (Adj[itr_1->n][p.n] > 0) {
				itr_1->degree -= 1;
			}
		}
		sort(R.begin(), R.end(), degCmp);
		minDeg = (R.end() - 1)->degree;
		itr = R.end() - 1;
		while (itr->degree == minDeg) {
			Rmin.push_back(*itr);
			if (itr == R.begin()) {
				break;
			}
			else {
				itr--;
			}
		}
	}
	return V;
}

#pragma endregion

#pragma region "Tree Search"

struct vertex {
	int n;
	int color;
};

bool colorCmp(vertex const & a, vertex const & b)
{
	return a.color < b.color;
}

bool Prune(double ** Adj, const vector<vertex> & candList, int Cmax, const vector<int> & S, double W, double Wmax, int & SL_better_count, int & CB_better_count, int & equal_count, double & bound_allweight) {
	bool prn = false;
	double W_prime = 0;
	double allweight = 0;
	int d = S.size();
	int n_candList = candList.size();
	if (d != 0) {
		vector<double> link(n_candList, 0);
		for (int i = 0; i < n_candList; i++) {
			for (int j = 0; j < d; j++) {
				link[i] += Adj[candList[i].n][S[j]];
			}
			allweight += link[i];
		}
		if (n_candList != 1) {
			int m_candList = 0;
			for (int i = 0; i < n_candList; i++) {
				for (int j = 0; j < n_candList; j++) {
					if (Adj[candList[i].n][candList[j].n] > 0) {
						m_candList++;
						allweight += 0.5 * Adj[candList[i].n][candList[j].n];
					}
				}
			}
			m_candList *= 0.5;
			if (m_candList != 0) {
				int t = Cmax;
				CB_better_count++;
				vector<vector<double>> contr(n_candList, vector<double>(n_candList + 1));
				for (int i = 0; i < n_candList; i++) {
					for (int j = 0; j < n_candList; j++) {
						contr[i][j] = 0.5 * Adj[candList[i].n][candList[j].n];
					}
					contr[i][n_candList] = link[i];
				}
				vector<double> max_contr(n_candList);
				for (int i = 0; i < n_candList; i++) {
					sort(contr[i].begin(), contr[i].begin() + n_candList);
					double temp = 0;
					for (int j = n_candList - t + 1; j < n_candList + 1; j++) {
						temp += contr[i][j];
					}
					max_contr[i] = temp;
				}
				sort(max_contr.begin(), max_contr.end());
				for (int i = n_candList - t; i < n_candList; i++) {
					W_prime += max_contr[i];
				}
			}
			else {
				W_prime = link[0];
				for (int i = 1; i < n_candList - 1; i++) {
					if (link[i] > W_prime) W_prime = link[i];
				}
			}
		}
		else {
			W_prime = link[0];
		}
	}
	else {
		if (n_candList != 1) {
			vector<int> deg(n_candList, 0);
			int m_candList = 0;
			for (int i = 0; i < n_candList; i++) {
				for (int j = 0; j < n_candList; j++) {
					if (Adj[candList[i].n][candList[j].n] > 0) {
						m_candList++;
						allweight += 0.5 * Adj[candList[i].n][candList[j].n];
					}
				}
			}
			m_candList *= 0.5;
			if (m_candList != 0) {
				int t = Cmax;
				CB_better_count++;
				vector<vector<double>> contr(n_candList, vector<double>(n_candList));
				for (int i = 0; i < n_candList; i++) {
					for (int j = 0; j < n_candList; j++) {
						contr[i][j] = 0.5 * Adj[candList[i].n][candList[j].n];
					}
				}
				vector<double> max_contr(n_candList);
				for (int i = 0; i < n_candList; i++) {
					sort(contr[i].begin(), contr[i].end());
					double temp = 0;
					for (int j = n_candList - t + 1; j < n_candList; j++) {
						temp += contr[i][j];
					}
					max_contr[i] = temp;
				}
				sort(max_contr.begin(), max_contr.end());
				for (int i = n_candList - t; i < n_candList; i++) {
					W_prime += max_contr[i];
				}
			}
			else {
				W_prime = 0;
				cout << "CHECK HERE (1)" << endl;
			}
		}
		else {
			W_prime = 0;
			cout << "CHECK HERE (2)" << endl;
		}
	}
	if (W_prime > allweight) {
		cout << "ERROR! -- WRONG BOUND" << endl;
	}
	bound_allweight += W_prime / allweight;
	if (W + W_prime <= Wmax) {
		prn = true;
	}
	return prn;
}

vector<vertex> Subcolor(double ** Adj, vector<vertex> & Uv) {
	vector<vertex> Lv(Uv.size());
	vector<vector<vertex>> C;
	vector<vertex> alaki(1);
	alaki[0].n = -1;
	alaki[0].color = -1;
	C.push_back(alaki);
	int maxNo = 0;
	for (vector<vertex>::iterator itr_1 = Uv.begin(); itr_1 != Uv.end(); itr_1++) {
		int k = 0;
		bool has_neighbor = true;
		while (has_neighbor == true) {
			if (C[k].size() == 1) {
				has_neighbor = false;
			}
			else {
				bool connected = false;
				for (vector<vertex>::iterator itr_2 = C[k].begin(); itr_2 != C[k].end(); itr_2++) {
					if (itr_2->n != -1) {
						if (Adj[itr_1->n][itr_2->n] > 0) {
							k += 1;
							connected = true;
							if (k > maxNo) {
								maxNo = k;
								C.push_back(alaki);
							}
							break;
						}
					}
				}
				if (connected == false) {
					has_neighbor = false;
				}
			}
		}
		C[k].push_back(*itr_1);
	}
	int i = 0;
	for (int k = 0; k < maxNo + 1; k++) {
		for (int j = 1; j < C[k].size(); j++) {
			Lv[i] = C[k][j];
			Lv[i].color = k + 1;
			i++;
		}
	}
	return Lv;
}

void BRANCH(double ** Adj, vector<vertex> & U, vector<vertex> & L, vector<int> & S, double & W, double & Wmax, int & count, int & SL_better_count, int & CB_better_count, int & equal_count, double & bound_allweight) {
	count++;
	while (!U.empty()) {
		vertex v;
		v.n = (L.end() - 1)->n;
		v.color = (L.end() - 1)->color;
		bool prn = Prune(Adj, U, v.color, S, W, Wmax, SL_better_count, CB_better_count, equal_count, bound_allweight);
		if (prn == false) {
			double addedWeight = 0;
			if (S.size() != 0) {
				for (vector<int>::iterator Sit = S.begin(); Sit != S.end(); Sit++) {
					addedWeight += Adj[*Sit][v.n];
				}
				W += addedWeight;
			}
			else {
				W = 0;
			}
			S.push_back(v.n);
			vector<vertex> Uv;
			for (vector<vertex>::iterator itr_1 = U.begin(); itr_1 != U.end(); itr_1++) {
				if (Adj[itr_1->n][v.n] > 0) {
					Uv.push_back(*itr_1);
				}
			}
			if (!Uv.empty()) {
				vector<vertex> Lv = Subcolor(Adj, Uv);
				BRANCH(Adj, Uv, Lv, S, W, Wmax, count, SL_better_count, CB_better_count, equal_count, bound_allweight);
			}
			else if (W > Wmax) {
				Wmax = W;
			}
			vector<int>::iterator itr = S.erase(S.end() - 1);
			W -= addedWeight;
		}
		else {
			return;
		}
		vector<vertex>::iterator Uit;
		if (U.size() == 1) {
			U.clear();
		}
		else {
			Uit = U.end() - 1;
			while (Uit != U.begin()) {
				if (Uit->n == v.n) {
					Uit = U.erase(Uit);
					break;
				}
				else {
					Uit -= 1;
				}
			}
		}
		if (L.size() == 1) {
			L.clear();
		}
		else {
			vector<vertex>::iterator Lit = L.end() - 1;
			Lit = L.erase(Lit);
		}
	}
	return;
}

#pragma endregion

int main()
{
	double A[N][N];
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			A[i][j] = 0;
		}
	}
	int s, t;
	ifstream data(GRAPH);
	while (data >> s >> t) {
		A[s - 1][t - 1] = ((s + t) % 200) + 1;
		A[t - 1][s - 1] = ((s + t) % 200) + 1;
	}
	double* Adj[N];
	for (int i = 0; i < N; i++) {
		Adj[i] = &A[i][0];
	}
	int count = 0;
	int SL_better_count = 0;
	int CB_better_count = 0;
	int equal_count = 0;
	double bound_allweight = 0.0;
	vector<int> S;
	double W = 0;
	double Wmax = double(InitialSol);
	int Delta;
	int* V = sortV(Adj, Delta);
	vector<vertex> U;
	vector<vertex> L;
	vertex u;
	for (int i = 0; i < Delta; i++) {
		u.n = V[i];
		u.color = i + 1;
		U.push_back(u);
		L.push_back(u);
	}
	for (int i = Delta; i < N; i++) {
		u.n = V[i];
		u.color = Delta + 1;
		U.push_back(u);
		L.push_back(u);
	}
	double cpu_1 = get_cpu_time();
	/****************************************************************************************************/
	BRANCH(Adj, U, L, S, W, Wmax, count, SL_better_count, CB_better_count, equal_count, bound_allweight);
	/****************************************************************************************************/
	double cpu_2 = get_cpu_time();
	cout << endl;
	cout << "==========================================================" << endl;
	cout << "                                                          " << endl;
	cout << "      A Combinatorial BnB Alg. for the MEWC Problem       " << endl;
	cout << "                                                          " << endl;
	cout << "==========================================================" << endl;
	cout << endl;
	cout << "INSTANCE :                " << GRAPH << endl;
	cout << endl;
	cout << "Max Weight :              " << Wmax << endl;
	cout << "CPU time (ms)  :          " << 1000 * (cpu_2 - cpu_1) << endl;
	cout << "----------------------------------------------------------" << endl;
	cout << "# of nodes :              " << count << endl;
	cout << endl;
	cout << "              ***  Quality of the Bound  ***              " << endl;
	cout << endl;
	cout << "Avg.  (Bound/Sum_weight) :       " << bound_allweight / (SL_better_count + CB_better_count + equal_count) << endl;
	cout << endl;
	cout << "# DB bound better (than CB) :    " << SL_better_count << endl;
	cout << "# two bound equal :              " << equal_count << endl;
	cout << "# CB bound better :              " << CB_better_count << endl;
	cout << endl;
	cout << "==========================================================" << endl;
};
