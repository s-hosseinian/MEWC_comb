/*________________________________________________________________________________________________________________
|                                                                                                                 |
|                                                                                                                 |
|               Analytic Bounds on Clique Number of Graphs + Vertex Coloring of Tomita&Kameda (2007)              |
|                                                                                                                 |
|                    Copyright (c) 2018 Seyedmohammadhossein Hosseinian. All rights reserved.                     |
|                                                                                                                 |
|_________________________________________________________________________________________________________________*/

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <cmath>
#include <Windows.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "mkl_lapacke.h"

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

LARGE_INTEGER getFILETIMEoffset() {
	SYSTEMTIME s;
	FILETIME f;
	LARGE_INTEGER t;

	s.wYear = 1970;
	s.wMonth = 1;
	s.wDay = 1;
	s.wHour = 0;
	s.wMinute = 0;
	s.wSecond = 0;
	s.wMilliseconds = 0;
	SystemTimeToFileTime(&s, &f);
	t.QuadPart = f.dwHighDateTime;
	t.QuadPart <<= 32;
	t.QuadPart |= f.dwLowDateTime;
	return (t);
}

int clock_gettime(int X, struct timeval *tv) {
	LARGE_INTEGER           t;
	FILETIME            f;
	double                  microseconds;
	static LARGE_INTEGER    offset;
	static double           frequencyToMicroseconds;
	static int              initialized = 0;
	static BOOL             usePerformanceCounter = 0;

	if (!initialized) {
		LARGE_INTEGER performanceFrequency;
		initialized = 1;
		usePerformanceCounter = QueryPerformanceFrequency(&performanceFrequency);
		if (usePerformanceCounter) {
			QueryPerformanceCounter(&offset);
			frequencyToMicroseconds = (double)performanceFrequency.QuadPart / 1000000.;
		}
		else {
			offset = getFILETIMEoffset();
			frequencyToMicroseconds = 10.;
		}
	}
	if (usePerformanceCounter) QueryPerformanceCounter(&t);
	else {
		GetSystemTimeAsFileTime(&f);
		t.QuadPart = f.dwHighDateTime;
		t.QuadPart <<= 32;
		t.QuadPart |= f.dwLowDateTime;
	}

	t.QuadPart -= offset.QuadPart;
	microseconds = (double)t.QuadPart / frequencyToMicroseconds;
	t.QuadPart = microseconds;
	tv->tv_sec = t.QuadPart / 1000000;
	tv->tv_usec = t.QuadPart % 1000000;
	return (0);
}

#pragma endregion

#pragma region "Initial Sort"

struct node {
	int n;
	int degree;
	int ex_deg;	//See definition of ex_deg(q) in Tomita(2007) page 101
};

bool degCmp(node const & a, node const & b)
{
	return a.degree > b.degree;
}

bool ex_degCmp(node const & a, node const & b)
{
	return a.ex_deg < b.ex_deg;
}

int* sortV(double** Adj, int & Delta, int N) {
	int* V = new int[N];
	vector<node> R;
	vector<node> Rmin;
	node v;
	int dlt = 0;
	for (int i = 0; i < N; i++) {
		v.n = i;
		v.degree = 0;
		for (int j = 0; j < N; j++) {
			if (Adj[i][j] > 0.0) {
				v.degree ++;
			}
		}
		if (v.degree > dlt) {
			dlt = v.degree;
		}
		R.push_back(v);
	}
	Delta = dlt;
	sort(R.begin(), R.end(), degCmp);
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
	node p;
	for (int k = N - 1; k >= 0; k--) {
		if (Rmin.size() == 1) {
			p = Rmin[0];
		}
		else {
			for (vector<node>::iterator itr_1 = Rmin.begin(); itr_1 != Rmin.end(); itr_1++) {
				itr_1->ex_deg = 0;
				for (vector<node>::iterator itr_2 = R.begin(); itr_2 != R.end(); itr_2++) {
					if (Adj[itr_1->n][itr_2->n] > 0.0) {
						itr_1->ex_deg += itr_2->degree;
					}
				}
			}
			sort(Rmin.begin(), Rmin.end(), ex_degCmp);
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
			if (Adj[itr_1->n][p.n] > 0.0) {
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

#pragma region "Utility"

int Subcolor(double ** Adj, vector<int> & U) {
	vector<vector<int>> C;
	vector<int> alaki(1);
	alaki[0]= -1;
	C.push_back(alaki);
	int maxNo = 0;
	for (vector<int>::iterator itr_1 = U.begin(); itr_1 != U.end(); itr_1++) {
		int k = 0;
		bool has_neighbor = true;
		while (has_neighbor == true) {
			if (C[k].size() == 1) {
				has_neighbor = false;
			}
			else {
				bool connected = false;
				for (vector<int>::iterator itr_2 = C[k].begin(); itr_2 != C[k].end(); itr_2++) {
					if (*itr_2 != -1) {
						if (Adj[*itr_1][*itr_2] > 0.0) {
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
	return (maxNo+1);
}

double* makeQ(double **Adj, int N) {
	double** Q = new double*[N];
	for (int i = 0; i < N; i++) {
		Q[i] = new double[N];
	}
	for (int i = 0; i<N; i++) {
		for (int j = 0; j<N; j++) {
			if (j<i) {
				Q[i][j] = 0;
			}
			else {
				Q[i][j] = Adj[i][j];
			}
		}
	}
	double* Q_a = new double[N*N];
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			Q_a[i*N + j] = Q[i][j];
		}
	}
	delete[] Q;
	return Q_a;
}

#pragma endregion

int main()
{
	// ************************************************************************************************************************************************************** RNG seed ***
	struct timeval ts;
	clock_gettime(1, &ts);
	srand(time(NULL) + ts.tv_usec);
	// ******************************************************************************************************************************************************** Initialization ***
	filebuf fb;
	fb.open("#output.txt", ios::out);
	ostream os(&fb);
	cout << endl;
	cout << "=====================================================" << endl;
	cout << "           Analytic Bounds on Clique Number          " << endl;
	cout << "=====================================================" << endl;
	cout << endl;
	os << endl;
	os << "=====================================================" << endl;
	os << "           Analytic Bounds on Clique Number          " << endl;
	os << "=====================================================" << endl;
	os << endl;
	int verNumber;
	string GRAPH;
	ifstream Data("instances.txt");
	while (Data >> verNumber >> GRAPH) {
		int N = verNumber;	
		// ********************************************************************************************************************** Generating the adjacency matrix of the graph ***
		int s, t;
		double** Adj = new double*[N];
		for (int i = 0; i < N; i++) {
			Adj[i] = new double[N];
		}
		for (int i = 0; i < N; i++) {
			for (int j = 0; j < N; j++) {
				Adj[i][j] = 0.0;
			}
		}
		ifstream data(GRAPH);
		while (data >> s >> t) {
			Adj[s - 1][t - 1] = 1.0;
			Adj[t - 1][s - 1] = 1.0;
		}
		// ********************************************************************************************************************* Tomita & Kameda (2007) Vertex-coloring Method ***
		double cpu_1 = get_cpu_time();
		int Tom_Kam = 0;
		for (int ir = 0; ir < 10; ir++) {
			int Delta;
			int* V = sortV(Adj, Delta, N);
			vector<int> U(N);
			int cc = 0;
			for (int i = 0; i < N; i++) {
				U[i] = V[i];
			}
			Tom_Kam = Subcolor(Adj, U);
		}
		// ********************************************************************************************************************************** Restricted Lagrangian Relaxation ***
		double cpu_2 = get_cpu_time();
		int upperBound = 0;
		for (int ir = 0; ir < 10; ir++) {
			vector<int> deg(N, 0);
			int m = 0;
			for (int i = 0; i < N; i++) {
				for (int j = 0; j < N; j++) {
					if (Adj[i][j] > 0) {
						deg[i]++;
						m++;
					}
				}
			}
			m *= 0.5;
			int K = 0;
			int temp = 0;
			for (int i = 0; i < N; i++) {
				temp = (2 * deg[i]) - (N - 1);
				if (temp > 0) {
					K += temp;
				}
			}
			K += (0.5 * N * (N - 1)) - m;
			upperBound = floor((1 + sqrt(1 + 4 * double(K))) / 2);
		}
		// ******************************************************************************************************************************************** Amin and Hakimi_degree ***
		double cpu_3 = get_cpu_time();
		int AH = 0;
		for (int ir = 0; ir < 10; ir++) {
			vector<int> degg(N, 0);
			int mm = 0;
			for (int i = 0; i < N; i++) {
				for (int j = 0; j < N; j++) {
					if (Adj[i][j] > 0) {
						degg[i]++;
						mm++;
					}
				}
			}
			mm *= 0.5;
			AH = floor((3 + sqrt(9 - 8 * double(N - mm))) / 2);
		}
		// ************************************************************************************************************************************************************** Wilf ***
		double cpu_4 = get_cpu_time();
		int wilf = 0;
		for (int ir = 0; ir < 10; ir++) {
			double* Q_a = makeQ(Adj, N);
			double* lambda = new double[N];
			MKL_INT n = N, lda = N, info;
			info = LAPACKE_dsyev(LAPACK_ROW_MAJOR, 'V', 'U', n, Q_a, lda, lambda);
			if (info > 0) {
				printf("The algorithm failed to compute eigenvalues.\n");
				exit(1);
			}
			double a = abs(lambda[0]);
			double b = abs(lambda[N - 1]);
			wilf = floor(a > b ? a : b) + 1;
		}
		// ****************************************************************************************************************************************** Amin and Hakimi_spectral ***
		double cpu_5 = get_cpu_time();
		int AHS = 0;
		for (int ir = 0; ir < 10; ir++) {
			int n_minusOne = 0;
			double* Q_aa = makeQ(Adj, N);
			double* lambdaa = new double[N];
			MKL_INT nn = N, ldaa = N, infoo;
			infoo = LAPACKE_dsyev(LAPACK_ROW_MAJOR, 'V', 'U', nn, Q_aa, ldaa, lambdaa);
			if (infoo > 0) {
				printf("The algorithm failed to compute eigenvalues.\n");
				exit(1);
			}
			for (int i = 0; i < N; i++) {
				if (lambdaa[i] <= -1) n_minusOne++;
			}
			AHS = n_minusOne + 1;
		}
		// ********************************************************************************************************************************************************** Budinich ***
		double cpu_6 = get_cpu_time();
		int Bud = 0;
		for (int ir = 0; ir < 10; ir++) {
			for (int i = 0; i < N; i++) {
				for (int j = 0; j < N; j++) {
					if (i != j) Adj[i][j] = 1.0 - Adj[i][j];
				}
			}
			double* Q_aaa = makeQ(Adj, N);
			double* lambdaaa = new double[N];
			MKL_INT nnn = N, ldaaa = N, infooo;
			infooo = LAPACKE_dsyev(LAPACK_ROW_MAJOR, 'V', 'U', nnn, Q_aaa, ldaaa, lambdaaa);
			if (infooo > 0) {
				printf("The algorithm failed to compute eigenvalues.\n");
				exit(1);
			}
			int n_naught = 0;
			for (int i = 0; i < N; i++) {
				if (abs(lambdaaa[i]) < 1e-13) { n_naught++; cout << "* "; }
			}
			Bud = floor(double(N + n_naught) / 2);
		}
		//************************************************************************************************************************************************************************
		double cpu_7 = get_cpu_time();
		os << endl;
		os << "Instance :         " << GRAPH << endl;
		os << "# vertices :       " << N << endl;
		//os << "edge density :     " << double(2*m)/double(N*(N-1)) << endl;
		os << "------------------------------------------" << endl;
		os << "Tomita & Kameda :  " << Tom_Kam << "\t CPU time (ms)  :  " << 1000 * (cpu_2 - cpu_1) << endl;
		os << "Our bound :        " << upperBound << "\t CPU time (ms)  :  " << 1000 * (cpu_3 - cpu_2) << endl;
		os << "Amin & Hakimi (1): " << AH << "\t CPU time (ms)  :  " << 1000 * (cpu_4 - cpu_3) << endl;
		os << "Wilf :             " << wilf << "\t CPU time (ms)  :  " << 1000 * (cpu_5 - cpu_4) << endl;
		os << "Amin & Hakimi (2): " << AHS << "\t CPU time (ms)  :  " << 1000 * (cpu_6 - cpu_5) << endl;
		os << "Budinich:          " << Bud << "\t CPU time (ms)  :  " << 1000 * (cpu_7 - cpu_6) << endl;
		os << endl;
		os << "==========================================" << endl;
		cout << endl;
		cout << "Instance :         " << GRAPH << endl;
		cout << "# vertices :       " << N << endl;
		//cout << "edge density :     " << double(2 * m) / double(N*(N - 1)) << endl;
		cout << "------------------------------------------" << endl;
		cout << "Tomita & Kameda :  " << Tom_Kam << "\t CPU time (ms)  :  " << 1000 * (cpu_2 - cpu_1) << endl;
		cout << "Our bound :        " << upperBound << "\t CPU time (ms)  :  " << 1000 * (cpu_3 - cpu_2) << endl;
		cout << "Amin & Hakimi (1): " << AH << "\t CPU time (ms)  :  " << 1000 * (cpu_4 - cpu_3) << endl;
		cout << "Wilf :             " << wilf << "\t CPU time (ms)  :  " << 1000 * (cpu_5 - cpu_4) << endl;
		cout << "Amin & Hakimi (2): " << AHS << "\t CPU time (ms)  :  " << 1000 * (cpu_6 - cpu_5) << endl;
		cout << "Budinich:          " << Bud << "\t CPU time (ms)  :  " << 1000 * (cpu_7 - cpu_6) << endl;
		cout << endl;
		cout << "==========================================" << endl;
		
	}
	fb.close();
	return 0;
}
