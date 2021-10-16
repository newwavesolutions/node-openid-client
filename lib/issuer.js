"use strict";

function asyncGeneratorStep(gen, resolve, reject, _next, _throw, key, arg) { try { var info = gen[key](arg); var value = info.value; } catch (error) { reject(error); return; } if (info.done) { resolve(value); } else { Promise.resolve(value).then(_next, _throw); } }

function _asyncToGenerator(fn) { return function () { var self = this, args = arguments; return new Promise(function (resolve, reject) { var gen = fn.apply(self, args); function _next(value) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "next", value); } function _throw(err) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "throw", err); } _next(undefined); }); }; }

/* eslint-disable max-classes-per-file */
const {
  inspect,
  deprecate
} = require('util');

const url = require('url');

const jose = require('jose');

const pAny = require('p-any');

const LRU = require('lru-cache');

const objectHash = require('object-hash');

const {
  RPError
} = require('./errors');

const getClient = require('./client');

const registry = require('./issuer_registry');

const processResponse = require('./helpers/process_response');

const webfingerNormalize = require('./helpers/webfinger_normalize');

const instance = require('./helpers/weak_cache');

const request = require('./helpers/request');

const {
  assertIssuerConfiguration
} = require('./helpers/assert');

const {
  ISSUER_DEFAULTS,
  OIDC_DISCOVERY,
  OAUTH2_DISCOVERY,
  WEBFINGER,
  REL,
  AAD_MULTITENANT_DISCOVERY
} = require('./helpers/consts');

const AAD_MULTITENANT = Symbol('AAD_MULTITENANT');

class Issuer {
  /**
   * @name constructor
   * @api public
   */
  constructor(meta = {}) {
    const aadIssValidation = meta[AAD_MULTITENANT];
    delete meta[AAD_MULTITENANT];
    ['introspection', 'revocation'].forEach(endpoint => {
      // if intro/revocation endpoint auth specific meta is missing use the token ones if they
      // are defined
      if (meta[`${endpoint}_endpoint`] && meta[`${endpoint}_endpoint_auth_methods_supported`] === undefined && meta[`${endpoint}_endpoint_auth_signing_alg_values_supported`] === undefined) {
        if (meta.token_endpoint_auth_methods_supported) {
          meta[`${endpoint}_endpoint_auth_methods_supported`] = meta.token_endpoint_auth_methods_supported;
        }

        if (meta.token_endpoint_auth_signing_alg_values_supported) {
          meta[`${endpoint}_endpoint_auth_signing_alg_values_supported`] = meta.token_endpoint_auth_signing_alg_values_supported;
        }
      }
    });
    Object.entries(meta).forEach(([key, value]) => {
      instance(this).get('metadata').set(key, value);

      if (!this[key]) {
        Object.defineProperty(this, key, {
          get() {
            return instance(this).get('metadata').get(key);
          },

          enumerable: true
        });
      }
    });
    instance(this).set('cache', new LRU({
      max: 100
    }));
    registry.set(this.issuer, this);
    Object.defineProperty(this, 'Client', {
      value: getClient(this, aadIssValidation)
    });
    Object.defineProperty(this, 'FAPIClient', {
      value: class FAPIClient extends this.Client {}
    });
  }
  /**
   * @name keystore
   * @api public
   */


  keystore(reload = false) {
    var _this = this;

    return _asyncToGenerator(function* () {
      assertIssuerConfiguration(_this, 'jwks_uri');
      const keystore = instance(_this).get('keystore');
      const cache = instance(_this).get('cache');

      if (reload || !keystore) {
        cache.reset();
        const response = yield request.call(_this, {
          method: 'GET',
          json: true,
          url: _this.jwks_uri
        });
        const jwks = processResponse(response);
        const joseKeyStore = jose.JWKS.asKeyStore(jwks, {
          ignoreErrors: true
        });
        cache.set('throttle', true, 60 * 1000);
        instance(_this).set('keystore', joseKeyStore);
        return joseKeyStore;
      }

      return keystore;
    })();
  }
  /**
   * @name queryKeyStore
   * @api private
   */


  queryKeyStore({
    kid,
    kty,
    alg,
    use,
    key_ops: ops
  }, {
    allowMulti = false
  } = {}) {
    var _this2 = this;

    return _asyncToGenerator(function* () {
      const cache = instance(_this2).get('cache');
      const def = {
        kid,
        kty,
        alg,
        use,
        key_ops: ops
      };
      const defHash = objectHash(def, {
        algorithm: 'sha256',
        ignoreUnknown: true,
        unorderedArrays: true,
        unorderedSets: true
      }); // refresh keystore on every unknown key but also only upto once every minute

      const freshJwksUri = cache.get(defHash) || cache.get('throttle');
      const keystore = yield _this2.keystore(!freshJwksUri);
      const keys = keystore.all(def);

      if (keys.length === 0) {
        throw new RPError({
          printf: ["no valid key found in issuer's jwks_uri for key parameters %j", def],
          jwks: keystore
        });
      }

      if (!allowMulti && keys.length > 1 && !kid) {
        throw new RPError({
          printf: ["multiple matching keys found in issuer's jwks_uri for key parameters %j, kid must be provided in this case", def],
          jwks: keystore
        });
      }

      cache.set(defHash, true);
      return new jose.JWKS.KeyStore(keys);
    })();
  }
  /**
   * @name metadata
   * @api public
   */


  get metadata() {
    const copy = {};
    instance(this).get('metadata').forEach((value, key) => {
      copy[key] = value;
    });
    return copy;
  }
  /**
   * @name webfinger
   * @api public
   */


  static webfinger(input) {
    var _this3 = this;

    return _asyncToGenerator(function* () {
      const resource = webfingerNormalize(input);
      const {
        host
      } = url.parse(resource);
      const webfingerUrl = `https://${host}${WEBFINGER}`;
      const response = yield request.call(_this3, {
        method: 'GET',
        url: webfingerUrl,
        json: true,
        query: {
          resource,
          rel: REL
        },
        followRedirect: true
      });
      const body = processResponse(response);
      const location = Array.isArray(body.links) && body.links.find(link => typeof link === 'object' && link.rel === REL && link.href);

      if (!location) {
        throw new RPError({
          message: 'no issuer found in webfinger response',
          body
        });
      }

      if (typeof location.href !== 'string' || !location.href.startsWith('https://')) {
        throw new RPError({
          printf: ['invalid issuer location %s', location.href],
          body
        });
      }

      const expectedIssuer = location.href;

      if (registry.has(expectedIssuer)) {
        return registry.get(expectedIssuer);
      }

      const issuer = yield _this3.discover(expectedIssuer);

      if (issuer.issuer !== expectedIssuer) {
        registry.delete(issuer.issuer);
        throw new RPError('discovered issuer mismatch, expected %s, got: %s', expectedIssuer, issuer.issuer);
      }

      return issuer;
    })();
  }
  /**
   * @name discover
   * @api public
   */


  static discover(uri) {
    var _this4 = this;

    return _asyncToGenerator(function* () {
      const parsed = url.parse(uri);

      if (parsed.pathname.includes('/.well-known/')) {
        const response = yield request.call(_this4, {
          method: 'GET',
          json: true,
          url: uri
        });
        const body = processResponse(response);
        return new Issuer({ ...ISSUER_DEFAULTS,
          ...body,
          [AAD_MULTITENANT]: !!AAD_MULTITENANT_DISCOVERY.find(discoveryURL => uri.startsWith(discoveryURL))
        });
      }

      const uris = [];

      if (parsed.pathname === '/') {
        uris.push(`${OAUTH2_DISCOVERY}`);
      } else {
        uris.push(`${OAUTH2_DISCOVERY}${parsed.pathname}`);
      }

      if (parsed.pathname.endsWith('/')) {
        uris.push(`${parsed.pathname}${OIDC_DISCOVERY.substring(1)}`);
      } else {
        uris.push(`${parsed.pathname}${OIDC_DISCOVERY}`);
      }

      return pAny(uris.map( /*#__PURE__*/function () {
        var _ref = _asyncToGenerator(function* (pathname) {
          const wellKnownUri = url.format({ ...parsed,
            pathname
          });
          const response = yield request.call(_this4, {
            method: 'GET',
            json: true,
            url: wellKnownUri
          });
          const body = processResponse(response);
          return new Issuer({ ...ISSUER_DEFAULTS,
            ...body,
            [AAD_MULTITENANT]: !!AAD_MULTITENANT_DISCOVERY.find(discoveryURL => wellKnownUri.startsWith(discoveryURL))
          });
        });

        return function (_x) {
          return _ref.apply(this, arguments);
        };
      }()));
    })();
  }
  /* istanbul ignore next */


  [inspect.custom]() {
    return `${this.constructor.name} ${inspect(this.metadata, {
      depth: Infinity,
      colors: process.stdout.isTTY,
      compact: false,
      sorted: true
    })}`;
  }

}
/**
 * @name key
 * @api private
 */


Issuer.prototype.key = deprecate( /*#__PURE__*/function () {
  var _key = _asyncToGenerator(function* ({
    kid,
    kty,
    alg,
    use,
    key_ops: ops
  }, allowMulti = false) {
    const cache = instance(this).get('cache');
    const def = {
      kid,
      kty,
      alg,
      use,
      key_ops: ops
    };
    const defHash = objectHash(def, {
      algorithm: 'sha256',
      ignoreUnknown: true,
      unorderedArrays: true,
      unorderedSets: true
    }); // refresh keystore on every unknown key but also only upto once every minute

    const freshJwksUri = cache.get(defHash) || cache.get('throttle');
    const keystore = yield this.keystore(!freshJwksUri);
    const keys = keystore.all(def);

    if (keys.length === 0) {
      throw new RPError({
        printf: ["no valid key found in issuer's jwks_uri for key parameters %j", def],
        jwks: keystore
      });
    }

    if (!allowMulti) {
      if (keys.length !== 1) {
        throw new RPError({
          printf: ["multiple matching keys found in issuer's jwks_uri for key parameters %j, kid must be provided in this case", def],
          jwks: keystore
        });
      }

      cache.set(defHash, true);
    }

    return keys[0];
  });

  function key(_x2) {
    return _key.apply(this, arguments);
  }

  return key;
}(), 'issuer.key is not only a private API, it is also deprecated');
module.exports = Issuer;