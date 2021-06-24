#include <cmath>
#include <iostream>
using namespace std;


//funkcja pomocnicza do liczenia tablic odwrotnoœci
int* reciprocal_table(int m_i, int w, int len) { //tablica odwrotnosci, gdzie parametrem jest m_i=2^w-ui, w-ilosc bitow, len-jak du¿a tab ma byæ wygen
	int* tab = new int[len];
	double reverse = 1.0 / m_i;  //  1/mi
	int w_pow = pow(2, w);   // 2^w
	for (int i = 0; i < len; i++) {
		reverse *= w_pow; //(1/mi)*2^w
		tab[i] = (int)reverse % w_pow;  //reszta z dzielenia przez 2^w
	}
	return tab; //zwrocenie kolejnych znakow dzielenia
}

//funkcja sing detection for power series
int SDPS(int X, int n, int w, int mi[]) { //jako paramtery przekazujemy X-liczbê, dla której liczymy znak,
	                                      //n-liczba liczb w bazie, w d³ugoœæ 2^w, mi to liczby odjête od 2^w, aby uzyskaæ bazê  
	int* B = new int[n]; //wektor B={m1...mn}
	int w_pow = pow(2, w); // zmienna 2^w
	for (int i = 0; i < n; i++) {
		B[i] = w_pow - mi[i]; //2^w-mi jako elementy naszej bazy
	}
	int* M_i = new int[n]; //Mi=M/mi, gdzie M to zakres dynamiczny M={m1*m2*...mn}
	for (int i = 0; i < n; i++) {
		M_i[i] = 1;
		for (int k = 0; k < n; k++)
			if (k != i)
				M_i[i] *= B[k];
	}

	int M = 1;
	for (int i = 0; i < n; i++)
		M *= B[i];  //zakres dynamiczny <-wymnozenie bazy
	int* x = new int[n]; //liczba wejœciowa
	for (int i = 0; i < n; i++)
		x[i] = X % B[i]; //reszty z poszczególnych baz xMODmi
	int* M_i_1 = new int[n];//liczba W
	for (int i = 0; i < n; i++) {
		for (int k = 0; k < B[i]; k++) {
			if (M_i[i] * k % B[i] == 1) {//odwrotnoœæ multiplikatywna z dzielenia Mi, gdzie Mi=M/mi
				M_i_1[i] = k; //sta³a wartoœæ dla danej bazy
				break;
			}
		}//dla kazdej pozycji w bazie sprawdzamy wszystkie dostepne cyfry
	}

	//-------------wlasciwy algorytm----------------
	int* eta = new int[n];
	for (int i = 0; i < n; i++) {
		eta[i] = (x[i] * M_i_1[i]) % B[i];  //mno¿enie modulo {x}_B*{W}_B
	}
	int gx_k = 0;
	for (int i = 0; i < n; i++)
		gx_k += eta[i];//suma wszystkich et
	int low = gx_k % w_pow;  //reszta z dzielenia z 2^w
	int sign = low >> (w - 1); //przesuniêcie bitowe   int sign=low/(w_pow/2)
	if (!sign) {//jeœli sign=0
		low = low + w_pow / 2; //zwiekszammy low o 2^(w-1)
	}
	int high = 0, z = 0, sum = 0, carry = 0; //deklaracja zmiennych
	for (int k = 0; k < n; k++) {
		gx_k = 0;
		for (int i = 0; i < n; i++) {
			int mi_pow = pow(mi[i], k);  //wyliczenie gx_k    , mi^k
			gx_k += mi_pow * eta[i];//suma wektora mi^k i et
		}
		high = gx_k >> w; //przesuniêcie o w bit
		z = high + low; //suma high i low
		sum = z % w_pow; //sum reszta z dzielenia 
		carry = z >> w;  //sprawdzenie czy z siê mieœci w ci¹gu w bitów
		if (carry == 1 || sum != w_pow - 1) { //jeœli siê nie mieœci to mamy overflow
			sign = sign ^ carry;// sign XOR carry
			break;
		}
		low = gx_k % w_pow; //do low przypisanie rezty z dzielnia gx_k przez 2^w
	}
	return sign;//zwrocenie znaku
}
int SDRT(int X) {
	int n = 3, w = 3;
	int mi[3] = { 3, 1, 0 };
	int w_pow = pow(2, w);
	int B[3];
	for (int i = 0; i < n; i++)
		B[i] = w_pow - mi[i];
	int x[3];
	for (int i = 0; i < n; i++)
		x[i] = X % B[i];
	int h1, h2, h3;
	int eta[3];
	int M_i_1[3];
	int M_i[3];
	for (int i = 0; i < n; i++) {
		M_i[i] = 1;
		for (int k = 0; k < n; k++)
			if (k != i)
				M_i[i] *= B[k];
	}
	for (int i = 0; i < n; i++) {
		for (int k = 0; k < B[i]; k++) {
			if (M_i[i] * k % B[i] == 1) {
				M_i_1[i] = k;
				break;
			}
		}
	}
	for (int i = 0; i < n; i++) {
		eta[i] = (x[i] * M_i_1[i]) % B[i];
	}
	int** h = new int* [n]; //dwuwyiarowa tab h
	for (int i = 0; i < n; i++)
		h[i] = reciprocal_table(B[i], w, n + 3); //h1 stanowi tab odwrotnosci  o d³ n+3
	h2 = 0;
	h3 = 0;
	for (int i = 0; i < n; i++) {
		h2 += eta[i]; //h2=sumie et
		h3 += eta[i] * h[i][1]; //eta *h_i(1)
	}
	int body, tail, sum, sign, carry;
	for (int k = 3; k < n + 3; k++) {
		h1 = h2;
		h2 = h3;
		h3 = 0;
		for (int i = 0; i < n; i++) //ponowne obliczenie h3
			h3 += h[i][k - 1] * eta[i]; //mno¿ênie wektorów, indeksujemy od 0, dlatego k-1
		if (k == 3) {
			body = h1 + (h2 >> w) + (h3 >> (2 * w));
			tail = body % 2; //tail jest parzystoœci¹ body
			sum = body % w_pow; //reszta z dzielenia 2^w z body
			sign = sum >> w - 1;//najwyzszy znaku sumy
			if (((sum % (w_pow / 2)) >> 1) != (w_pow / 4) - 1) //je¿eli resztta z dzielenia sumy przez 2^(w-1) przesuniete o 1 nie równa sie 2^(w-2) -1
				return sign; //zwracamy znak
		}
		else {//w przeciwnym wypadku wracamy do pêtli i dla body przypisujemt
			body = (h1 % w_pow) + ((h2 >> w) % w_pow) + ((h3 >> (2 * w)) % w_pow); //h1mod2^w + h2 przesunêie bitowo o w modulo 2^w +h3 przesunêie bitowo o 2w modulo 2^w
			int tmp = (body + tail * w_pow) >> 1; //body i tail(najwy¿szy znak) *2^w przesuniete o 1
			tail = body % 2; //nowy tail
			carry = tmp >> w;//tmp przesunite o w, czyli te¿ podzielone przez 2^w
			sum = tmp % w_pow; //reszta z dzielenia z tmp przez 2^w
			if (carry == 1 || sum != w_pow - 1) { //sprawdzanie je¿eli carry jest rowne 1 albo suma nie rowna sie 2^w-1
				sign = sign ^ carry; //do znaku przypisujemy signXOR carry
				return sign;//zwracamy znak
			}
		}
	}
	return sign;
}


int SDPS_(int X) {
	int B[] = { 13,15,16 }; //w=4, 2^w=16
	int Mi[] = { 15*16, 13*16, 13*15 };
	int M = 13*15*16; //3120
	int r[3] = { 3,1,0 };
	int x[3];
	for (int i = 0; i < 3; i++)
		x[i] = X % B[i];
	int Mi_1[3];
	for (int i = 0; i < 3; i++) {
		for (int k = 0; k < B[i]; k++) {
			if (Mi[i] * k % B[i] == 1) {
				Mi_1[i] = k;
				break;
			}
		}
	}
	int eta[3];
	int w = 4;
	int w_pow = pow(2, w);
	int w_pow_m = pow(2, w - 1);
	for (int i = 0; i < 3; i++)
		eta[i] = (x[i] * Mi_1[i]) % B[i];
	int gx_k = 0;
	for (int i = 0; i < 3; i++)
		gx_k += eta[i];
	int low = gx_k % w_pow;
	int sign = low >> (w-1);
	if (!sign) {
		low = low + w_pow_m;
	}
	int high = 0, z = 0, sum = 0, carry = 0;
	for (int k = 0; k < 3; k++) {
		gx_k = 0;
		for (int i = 0; i < 3; i++) {
			int mi_pow = r[i];
			for (int j = 0; j < k; j++)
				mi_pow *= mi_pow;
			gx_k += mi_pow * eta[i];
		}
		high = gx_k >> w;
		z = high + low;
		sum = z % w_pow;
		carry = z >> w;
		if (carry == 1 || sum != (w_pow-1)) {
			sign = sign ^ carry;
			break;
		}
		low = gx_k % w_pow;
	}
	return sign;
}


int main() {
	int cnt = 0;
	int M = 13*16*15;
	//int* tab = new int[cnt];
	for (int i = 0; i < M; i++) {
		int sign = SDRT(i);
		if (i < (M/2)) {
			if (sign != 0)  //sprawdzanie b³êdów
				
				//cout << i << endl;
				cnt++;
		}
		
		else
			if (sign != 1)
			//cout << i << endl;	
		   cnt++;
		
	}
	cout << cnt ;
	//cout << SDRT(1)<<endl;

	

	
	return 0;
}