/*-------------------------------------------------------------------------
                    _      _   _             _    
 __ ___ _ _ _ _ ___| |__ _| |_(_)___ _ _    (_)___
/ _/ _ \ '_| '_/ -_) / _` |  _| / _ \ ' \ _ | (_-<
\__\___/_| |_| \___|_\__,_|\__|_\___/_||_(_)/ /__/
                                          |__/  
Version 1.0, October 28 2014
-------------------------------------------------------------------------*/
/*
Perform complex signal correlation on control-rate data.

arguments: <int>sample size <float>overlap percent <symbol> window function

inlet 0 : signal a. <float> for real-valued signal or 
                    <list>  (real, imag) for complex signal

inlet 1 : signal b. <float> for real-valued signal or 
                    <list>  (real, imag) for complex signal


outlet 0: <list> real part of correlation

outlet 1: <list> imag part of correlation

outlet 2 <list> (real, imag) time-lag

outlet 3 <list> (real, imag) correlation strength

outlet 4 <list> sample rate.

public methods:

set_window_function <symbol> ('hamming' | 'hann' | 'blackman' | 'rectangle')
  set the analysis window function. rectangle by default

set_overlap <float> (0 ~ 100) 
  the percent that each analysis frame should overlap the previous frame.
  default 87.5% (7/8).

set_should_normalize <int> (0 ~ 1) 
  if 1, each analysis frame of each signal will be normalized prior to 
  correlation. this is done by subtracting out the mean and multiplying 
  by the standard deviation. default 0.

set_should_produce_polar_output <int> (0 ~ 1) 
  if 1, output will be in polar rather than rectangular form. default 1.

Discussion:
This makes use of the convolution property which says 
the the Fourier Transform converts convolution
into multiplication, and correlation into cojugation
and multiplication. So, the signals are windowed, 
transformed, multiplied, and inverse-transformed.

This implementation is optimized to avoid explicit bit-
reversal by using a decimation-in-frequency form of fft
for forward transform and a decimation-in-time form for
inverse. The signal multiplication is done in bit-reversed
order.

The Max / Javascript implementation of sin() is more efficient
than anything that can be implemented in javascript. It was
tested to run 50,000 times with arguments ranging from 0 
to 2pi in about 32 milliseconds. An unrolled Taylor-series
js implementation calculating 5 terms (including x^9 / 9!) 
tested under the same conditions ran in about 45 milliseconds.
A table lookup in 4096-point array using 32-bit fixed-point 
angle ran in about 34 milliseconds.

Made by Michael Krzyzaniak at the Synthesis Center
Under the direction of Sha Xin Wei, at Arizona State
University's School of Arts, Media + Engineering 
in Fall of 2014.

mkrzyzan@asu.edu
*/

/*-----------------_------------__--__-_-----------------------------------
 __ ___ _ __  _ __| |_____ __  / _|/ _| |_ 
/ _/ _ \ '  \| '_ \ / -_) \ / |  _|  _|  _|
\__\___/_|_|_| .__/_\___/_\_\ |_| |_|  \__|
             |_|      
-------------------------------------------------------------------------*/
function fft_complex_signal(N)
{
  this.real  = new Array(N);
  this.imag  = new Array(N);
  this.rho   = this.real;
  this.theta = this.imag;
  
  var i
  for(i=0; i<N; i++)
    this.real[i] = this.imag[i] = 0;
  
  return this;
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.copy = function()
{
  var c = new fft_complex_signal(0);
  c.real = this.real.slice(0, this.real.length);
  c.imag = this.imag.slice(0, this.imag.length);
  c.rho   = c.real;
  c.theta = c.imag;
  return c;
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.correlate = function(signal_b)
{
  // this function is the link between the public interface
  // and the under-the-hood fft implementation. as such, it
  // uses several 'global' instance variables that are declared 
  // in the public interface below.

  var temp;
  var a = this.copy();
  var b = signal_b.copy();  

  if(should_normalize)
    {
      a.normalize();
      b.normalize();	
    }

  a.apply_window(analysis_window);
  b.apply_window(analysis_window);
  a.zero_pad(fft_size);
  b.zero_pad(fft_size);
  a.fft_decimation_in_frequency(false);
  b.fft_decimation_in_frequency(false); 

  
  var i, temp;
  for(i=0; i<fft_size; i++)
    {
	  temp      = (a.real[i] * b.real[i]) + (a.imag[i] * b.imag[i]);
	  a.imag[i] = (b.real[i] * a.imag[i]) - (a.real[i] * b.imag[i]);  
	  a.real[i] = temp;
    }

  a.fft_decimation_in_time(true); 
    
  //what about DC?
  for(i=0; i<(fft_size * 0.5); i++)
    {
      a.real.push(a.real.shift());
      a.imag.push(a.imag.shift());
    }

  if(should_polar_output)
    a.cartesian_to_polar();

  return a;
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.bit_reverse_indices = function()
{
  var N = this.real.length;
  var N_minus_1 = N-1;
  var highest_bit = N >> 1;
  var n, next_bit, n_reversed=0;
  var temp;
  
  for(n=1; n<N; n++)
    {
      next_bit = highest_bit;
      while((next_bit + n_reversed) > N_minus_1) next_bit >>= 1;  //find highest unpopulated bit
      n_reversed &= next_bit - 1;                                 //clear all higher bits
      n_reversed |= next_bit;                                     //set new bit
      
      if(n_reversed > n)
        {
          temp                  = this.real[n]         ;
          this.real[n]          = this.real[n_reversed];
          this.real[n_reversed] = temp                 ;
          temp                  = this.imag[n]         ;
          this.imag[n]          = this.imag[n_reversed];
          this.imag[n_reversed] = temp                 ;          
        }
    }
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.fft_decimation_in_time = function(isInverse)
{ 
  //takes input in bit-reversed order
  var N = this.real.length;
  var two_pi_over_N = Math.TWO_PI / N;
  var omega_two_pi_over_n;
  var sub_transform, butterfly;
  
  var num_sub_transforms = N, num_butterflies = 1, omega;
  var wr, wi, r=this.real, i=this.imag, tempr, tempi;

  var array_offset = 0;
  
  while((num_sub_transforms >>= 1) > 0)
    {
	  array_offset = 0;
      for(sub_transform=0; sub_transform<num_sub_transforms; sub_transform++)
        {
          omega = 0;
          for(butterfly=0; butterfly<num_butterflies; butterfly++)
            {
              omega_two_pi_over_n = omega * two_pi_over_N;
              tempr   =  Math.cos(omega_two_pi_over_n);
              tempi   = -Math.sin(omega_two_pi_over_n);
              if(isInverse)
                tempi = -tempi;
              wr = (r[num_butterflies + array_offset] * tempr) - (i[num_butterflies + array_offset] * tempi);
              wi = (r[num_butterflies + array_offset] * tempi) + (i[num_butterflies + array_offset] * tempr);
              tempr = r[array_offset]; tempi = i[array_offset];
              r[array_offset] += wr;
              i[array_offset] += wi;
              r[num_butterflies + array_offset] = tempr - wr;
              i[num_butterflies + array_offset] = tempi - wi;
              omega += num_sub_transforms;
              array_offset++;
            }
            array_offset += num_butterflies;
        }
      num_butterflies <<= 1;
    }
 
    if(isInverse)
      {
        for(omega=0; omega<N; omega++)
          {
            r[omega] /= N;
            i[omega] /= N;
          }
      }
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.fft_decimation_in_frequency = function(isInverse)
{
  //produces output in bit-reversed order
  var N = this.real.length;
  var two_pi_over_N = Math.TWO_PI / N;
  var omega_two_pi_over_n;
  var sub_transform, butterfly;
  
  var num_sub_transforms = 1, num_butterflies = N/2, omega;
  var wr, wi, r=this.real, i=this.imag, tempr, tempi;

  var array_offset = 0;
  
  while(num_sub_transforms < N)
    {
	  array_offset = 0;
      for(sub_transform=0; sub_transform<num_sub_transforms; sub_transform++)
        {
          omega = 0;
          for(butterfly=0; butterfly<num_butterflies; butterfly++)
            {
              omega_two_pi_over_n = omega * two_pi_over_N;
              wr   =  Math.cos(omega_two_pi_over_n);
              wi   = -Math.sin(omega_two_pi_over_n);
              if(isInverse)
                wi = -wi;
              
              tempr = r[array_offset];
              tempi = i[array_offset];
              r[array_offset] += r[num_butterflies + array_offset];
              i[array_offset] += i[num_butterflies + array_offset];
              r[num_butterflies + array_offset] = tempr - r[num_butterflies + array_offset];
              i[num_butterflies + array_offset] = tempi - i[num_butterflies + array_offset];
              tempr = (r[num_butterflies + array_offset] * wr) - (i[num_butterflies + array_offset] * wi);
              tempi = (r[num_butterflies + array_offset] * wi) + (i[num_butterflies + array_offset] * wr)
              r[num_butterflies + array_offset] = tempr;
              i[num_butterflies + array_offset] = tempi;

              omega += num_sub_transforms;
              array_offset++;
            }
            array_offset += num_butterflies;
        }
      num_sub_transforms <<= 1;
      num_butterflies    >>= 1;
    }
 
    if(isInverse)
      {
        for(omega=0; omega<N; omega++)
          {
            r[omega] /= N;
            i[omega] /= N;
          }
      }
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.cartesian_to_polar = function()
{
  var i, rho, theta;
  for(i=0; i<this.real.length; i++)
    {
      rho =   Math.hypot(this.real[i], this.imag[i]);
      theta = Math.atan2(this.imag[i], this.real[i]);
      this.real[i] = rho;
      this.imag[i] = theta;
    }
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.polar_to_cartesian = function(signal)
{
  var i, real, imag;
  for(i=0; i<this.rho.length; i++)
    {
      real = this.rho[i] * Math.cos(this.theta[i]);
      imag = this.rho[i] * Math.sin(this.theta[i]);
      this.rho[i]   = real;
      this.theta[i] = imag;
    }
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.normalize = function()
{
  real_normalize_signal(this.real);
  real_normalize_signal(this.imag);
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.zero_pad = function(length)
{
  while(this.real.length < length)
    {
      this.real.push(0);
      this.imag.push(0);	
    }
}

/*-----------------------------------------------------------------------*/
fft_complex_signal.prototype.apply_window = function(window)
{
  for(i=0; i<window.length; i++)
    {
      this.real[i] *= window[i];
      this.imag[i] *= window[i];
    }
  for(i=window.length; i<this.real.length; i++)
    {
      this.real[i] = 0;
      this.imag[i] = 0;
    }
}

/*------_---------_--------------------------------------------------------            
__ __ _(_)_ _  __| |_____ __ _____
\ V  V / | ' \/ _` / _ \ V  V (_-<
 \_/\_/|_|_||_\__,_\___/\_/\_//__/
-------------------------------------------------------------------------*/
function fft_make_rect_window(buffer, n)
{
  var i;
  for(i=0; i<n; i++)
    buffer[i] = 0.5;
}

/*-----------------------------------------------------------------------*/
function fft_make_hann_window(buffer, n)
{
  var i;
  var phase = 0;
  var phase_increment = Math.TWO_PI / n;
  for(i=0; i<n; i++)
    {
      buffer[i] = 0.5 * (1-Math.cos(phase));
      phase += phase_increment;
    }  
}

/*-----------------------------------------------------------------------*/
function fft_make_hamming_window(buffer, n)
{
  var i;
  var phase = 0;
  var phase_increment = Math.TWO_PI / n;
  for(i=0; i<n; i++)
    {
      buffer[i] = 0.54 - (0.46 * Math.cos(phase));
      phase += phase_increment;
    }  
}

/*-----------------------------------------------------------------------*/
function fft_make_blackman_window(buffer, n)
{
  var i;
  var phase = 0;
  var phase_increment = Math.TWO_PI / n;
  var a = 0.16;
  var a0 = (1-a)/2.0;
  var a1 = 1/2.0;
  var a2 = a/2.0;
  
  for(i=0; i<n; i++)
    {
      buffer[i] = a0 - (a1 * Math.cos(phase)) + (a2 * Math.cos(2*phase));
      phase += phase_increment;
    }  
}

/*--------_----------------------------------------------------------------
| |_  ___| |_ __  ___ _ _ ___
| ' \/ -_) | '_ \/ -_) '_(_-<
|_||_\___|_| .__/\___|_| /__/
           |_|   
-------------------------------------------------------------------------*/
Math.TWO_PI = 2 * Math.PI;
Math.hypot =  function(x, y){return Math.sqrt((x*x)+(y*y))};

/*-----------------------------------------------------------------------*/
Array.prototype.index_of_largest_item = function()
{
  var largest = this[0];
  var result = 0;
  var i;

  for(i=1; i<this.length; i++)
    {
      if(this[i] > largest)
        {
          result = i;
          largest = this[i];
        }
    }
  return result;
}

/*-----------------------------------------------------------------------*/
function nearest_power_of_two(n)
{
  var result = 1;
  while(result < n)
    result <<= 1;
  return result;
}

/*-----------------------------------------------------------------------*/
function real_normalize_signal(signal)
{
  var mean=0, standard_deviation=0;
  var i;
  
  for(i=0; i<signal.length; i++)
    mean += signal[i];
  mean /= signal.length;  

  for(i=0; i<signal.length; i++)
    {
      signal[i] -= mean;
      standard_deviation += signal[i] * signal[i];
    }
  //there are N-1 independent observarions aside from the mean
  standard_deviation /= signal.length - 1;
  standard_deviation = Math.sqrt(standard_deviation);

  if(standard_deviation != 0)
    {
      for(i=0; i<signal.length; i++)
        signal[i] /= standard_deviation;
    }
}

/*------_-_---_------_-_---------_---_-------------------------------------        
(_)_ _ (_) |_(_)__ _| (_)_____ _| |_(_)___ _ _  
| | ' \| |  _| / _` | | |_ / _` |  _| / _ \ ' \ 
|_|_||_|_|\__|_\__,_|_|_/__\__,_|\__|_\___/_||_|
-------------------------------------------------------------------------*/
inlets  = 2;
outlets = 5;

var SIGNAL_A_INLET             = 0;
var SIGNAL_B_INLET             = 1;

var R_OUTLET                   = 0;
var I_OUTLET                   = 1;
var LAG_OUTLET                 = 2;
var CORRELATION_VECTOR_OUTLET  = 3;
var SAMPLE_INTERVAL_OUTLET     = 4;

setinletassist(SIGNAL_A_INLET, "signal A -- float{real}, list{real, imag}, or list{w, x, y, z}");
setinletassist(SIGNAL_B_INLET, "signal B -- float{real}, list{real, imag}, or list{w, x, y, z}");

setoutletassist(R_OUTLET,   "correlation real or magnitude");
setoutletassist(I_OUTLET,   "correlation imag or angles");
setoutletassist(LAG_OUTLET, "time lag");
setoutletassist(CORRELATION_VECTOR_OUTLET,   "correlation vector");

setoutletassist(SAMPLE_INTERVAL_OUTLET, "signal A sample interval");
//setoutletassist(FREQ_OUTLET, "estimation of fundamental");


var input_size = 64;
var overlap_percent = 87.5;
var window_function_name = "rectangle";

if(jsarguments.length > 1)
  input_size = jsarguments[1];
if(jsarguments.length > 2)
  overlap_percent = jsarguments[2];
if(jsarguments.length > 3)
  window_function_name = jsarguments[2];

var input_counter      = 0;
var complex_input_a    = new fft_complex_signal   (input_size);
var complex_input_b    = new fft_complex_signal   (input_size);
var analysis_window    = new Array(input_size);

var one_minus_overlap_num_samples;
var should_normalize    = false;
var should_polar_output = true;
var sample_interval     = 0;
var prev_sample_time    = 0;

var fft_size   = nearest_power_of_two(2 * input_size);

set_window_function(window_function_name);
set_overlap(overlap_percent);

/*---------_------_------_-----_------------__-----------------------------      
 _ __ _  _| |__| (_)__  (_)_ _| |_ ___ _ _ / _|__ _ __ ___ 
| '_ \ || | '_ \ | / _| | | ' \  _/ -_) '_|  _/ _` / _/ -_)
| .__/\_,_|_.__/_|_\__| |_|_||_\__\___|_| |_| \__,_\__\___|
|_| 
-------------------------------------------------------------------------*/
function bang(n)
{

}

/*-----------------------------------------------------------------------*/
function msg_int(n)
{
  msg_float(n);
}

/*-----------------------------------------------------------------------*/
function msg_float(n)
{
  list(n);
}

/*-----------------------------------------------------------------------*/
function list()
{
  var a = arrayfromargs(arguments);
  var input_signals, input;
  
  switch(a.length)
    {
      case 1:
        a.push(0);
        //cascade
  	  case 2:
  	    input_signals = [complex_input_a, complex_input_b];
  	    input = input_signals[inlet];
  	    input.real.shift();
  	    input.imag.shift();
  	    input.real.push(a[0]);
  	    input.imag.push(a[1]);
  	    break;
  	  default: break
    }
  
  if(inlet == SIGNAL_A_INLET)
    {
	  //update sample rate
      var t  = max.time;
      var dt = t - prev_sample_time;
      if(dt < 500) sample_interval = (sample_interval * 0.9) + (dt * 0.1);
      prev_sample_time = t;
      ++input_counter; input_counter %= one_minus_overlap_num_samples;

      if (input_counter == 0)
        {
  	      var result = input_signals[0].correlate(input_signals[1]);
          var lag_index = result.real.index_of_largest_item();
          outlet(SAMPLE_INTERVAL_OUTLET, sample_interval);
          outlet(CORRELATION_VECTOR_OUTLET, result.real[lag_index], result.imag[lag_index]);
          outlet(LAG_OUTLET, (lag_index - (fft_size * 0.5)) * sample_interval);
          outlet(I_OUTLET,   result.imag);
  	      outlet(R_OUTLET,   result.real);
        }
  	}
}

/*-----------------------------------------------------------------------*/
function set_should_produce_polar_output(n)
{
  should_polar_output = (n != 0);
}

/*-----------------------------------------------------------------------*/
function set_window_function(name_of_function /*rectangle, hann, hamming, blackman*/)
{
  var window_funct;

  switch(name_of_function)
    {
      case "hann"     : window_funct = fft_make_hann_window     ; break;
      case "hamming"  : window_funct = fft_make_hamming_window  ; break;
      case "blackman" : window_funct = fft_make_blackman_window ; break;
      default         : window_funct = fft_make_rect_window     ; break;
    }

  window_funct(analysis_window, input_size);
}

/*-----------------------------------------------------------------------*/
function set_should_normalize(n)
{
  should_normalize = (n != 0);
}

/*-----------------------------------------------------------------------*/
function set_overlap(n)
{
  if(n > 100) n = 100;
  if(n < 0)   n = 0;
  n *= 0.01;
  n = 1.0 - n;
  n *= input_size;
  
  if(n < 1) n = 1;
  if(n > input_size) n = input_size;
  
  one_minus_overlap_num_samples = parseInt(n);
}

/*----------_----------------------------------------------_---------------
 __ ___  __| |___   __ _ _ _ __ ___ _____ _  _ __ _ _ _ __| |
/ _/ _ \/ _` / -_) / _` | '_/ _` \ V / -_) || / _` | '_/ _` |
\__\___/\__,_\___| \__, |_| \__,_|\_/\___|\_, \__,_|_| \__,_|
                   |___/                  |__/  
-------------------------------------------------------------------------*/                   
/*
STFT.prototype.findFundamental = function()
{
  //assumes polar coords;
  var highest     =-1, secondHighest     =-1;
  var highestIndex= 0, secondHighestIndex= 0;
  var i;

  //don't consider the DC component a frequency
  for(i=1; i<(this.numSamples/2.0); i++)
    {
      if(this.real[i] > highest)
        {
	      secondHighest = highest;
	      highest = this.real[i];
	      secondHighestIndex = highestIndex;
	      highestIndex = i;
        }
      else if(this.real[i] > secondHighest)
        {
	      secondHighest = this.real[i];
	      secondHighestIndex = i;
        }
    }
  return vertexOfParabolaPassingThroughPoints(highestIndex, highest, secondHighestIndex, secondHighest);
}
*/

/*-----------------------------------------------------------------------*/
/*
function vertexOfParabolaPassingThroughPoints(x1, y1, x2, y2)
{
  if(y1 == 0) return 0;  

  //should be y1 / y2 but this inverts points to find correct frequency  
  v =  Math.sqrt(y2) / Math.sqrt(y1);

  return (x1 + (v*x2)) / (1 + v);
}
*/

/*-----------------------------------------------------------------------*/
/*
STFT.prototype.scaleMagnitudes = function(min, max)
{
  var minSample = new Number(1000000);
  var maxSample = 0;
  var i;
  
  for(i=0; i<this.N; i++)
    {
      if(this.realeal[i] < minSample)
        minSample = this.realeal[i];
      if(this.realeal[i] > maxSample)
        maxSample = this.realeal[i];
    }
    
  for(i=0; i<this.N; i++)
    this.realeal[i] = scalef(this.realeal[i], minSample, maxSample, min, max);
}

function scalef(x, in_min, in_max, out_min, out_max)
{
  return (((x - in_min) * (out_max - out_min)) / (in_max - in_min)) + out_min;
}
*/
