#include "basis_pms.h"
#include "build.h"
#include "pms.h"
#include "heuristic.h"
#include <signal.h>

ISDist s;
int seed = 1;
long long best_known;
long long total_step = 0;
long long consecutive_better_soft = 0;
char * file_name = NULL;
void interrupt(int sig)
{
	if (s.verify_sol() == 1)
		cout << "c verified" << endl;
	s.print_best_solution();
	s.free_memory();
	exit(10);
}

int main(int argc, char *argv[])
{
	start_timing();

	signal(SIGTERM, interrupt);

	// sscanf(argv[2], "%d", &seed);
	// seed = 1;
	// srand(seed);
	s.build_instance(argv[1]);

	s.settings();

	s.parse_parameters2(argc, argv);
	s.local_search_with_decimation(argv[1]);

	s.simple_print(argv[1]);

	//s.free_memory();

	return 0;
}
